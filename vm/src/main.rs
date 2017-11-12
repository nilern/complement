#![feature(unboxed_closures, try_from)]

#[macro_use]
extern crate gc_derive;
extern crate gc;
extern crate clap;

use gc::Gc;

use value::ValueRef;
use bytecode::Instr;
    
#[derive(Debug)]
pub enum VMError {
    OutOfInstrs,
    Uninitialized,
    Type,
    Bounds
}
    
#[derive(Debug, Trace, Finalize)]
pub struct Program {
    register_demand: usize,
    procs: Vec<Gc<Proc>>,
    entry: usize
}

#[derive(Debug, Trace, Finalize)]
pub struct Proc {
    name: String,
    consts: Vec<ValueRef>,
    #[unsafe_ignore_trace]
    instrs: Vec<Instr>
}

mod value { /**************************************************************************************/
    use std::convert::TryFrom;
    use std::collections::HashMap;
    use gc::{Gc, GcCell};

    use super::{Proc, VMError};
    
    pub type ValueRef = Gc<Value>;
    
    #[derive(Debug, Trace, Finalize)]
    pub struct Tuple { pub fields: GcCell<Vec<ValueRef>> }
    
    #[derive(Debug, Trace, Finalize)]
    pub struct VMBox { pub value: GcCell<ValueRef> }
    
    #[derive(Debug, Trace, Finalize)]
    pub struct CodePtr {
        pub cob: Gc<Proc>,
        pub pc: usize
    }
    
    #[derive(Debug, Trace, Finalize)]
    pub struct Closure {
        pub code: GcCell<Gc<Value>>,
        pub env: GcCell<Vec<ValueRef>>
    }

    #[derive(Debug, Trace, Finalize)]
    pub struct Record {
        pub typ: GcCell<Gc<Value>>,
        pub fields: GcCell<Vec<ValueRef>>
    }
    
    #[derive(Debug, Trace, Finalize)]
    pub enum Value {
        Int(isize),
        Char(char),
        Bool(bool),
        
        Symbol(String),
        String(String),
    
        Tuple(Tuple),
    
        Null,
        Box(VMBox),
        
        CodePtr(CodePtr),
        Fn(Closure),
        Cont(Closure),
        
        Denv(HashMap<String, ValueRef>),

        Record(Record)
    }
    
    impl Value {
        pub fn new_tuple(len: usize) -> Value {
            Value::Tuple(Tuple { fields: GcCell::new(vec![Gc::new(Value::Null); len]) })     
        }
    
        pub fn new_box() -> Value {
            Value::Box(VMBox { value: GcCell::new(Gc::new(Value::Null)) })
        }
        
        pub fn new_code_ptr(cob: Gc<Proc>, pc: usize) -> Value {
            Value::CodePtr(CodePtr {
                cob: cob,
                pc: pc
            })
        }
    
        pub fn new_fn(len: usize) -> Value {
            Value::Cont(Closure {
                code: GcCell::new(Gc::new(Value::Null)),
                env: GcCell::new(vec![Gc::new(Value::Null); len])
            })
        }
        
        pub fn new_cont(len: usize) -> Value {
            Value::Cont(Closure {
                code: GcCell::new(Gc::new(Value::Null)),
                env: GcCell::new(vec![Gc::new(Value::Null); len])
            })
        }
    
        pub fn new_denv() -> Value {
            Value::Denv(HashMap::new())     
        }

        pub fn new_record(len: usize) -> Value {
            Value::Record(Record {
                typ: GcCell::new(Gc::new(Value::Null)),
                fields: GcCell::new(vec![Gc::new(Value::Null); len])
            })
        }
    }
    
    impl<'a> TryFrom<&'a Value> for isize {
        type Error = VMError;
    
        fn try_from(v: &Value) -> Result<isize, VMError> {
            if let &Value::Int(i) = v { Ok(i) } else { Err(VMError::Type) }
        }
    }
    
    impl<'a> TryFrom<&'a Value> for usize {
        type Error = VMError;
    
        fn try_from(v: &Value) -> Result<usize, VMError> {
            if let &Value::Int(i) = v { Ok(i as usize) } else { Err(VMError::Type) }
        }
    }
    
    impl<'a> TryFrom<&'a Value> for bool {
        type Error = VMError;
    
        fn try_from(v: &Value) -> Result<bool, VMError> {
            if let &Value::Bool(b) = v { Ok(b) } else { Err(VMError::Type) }
        }
    }
    
    impl<'a> TryFrom<&'a Value> for &'a Tuple {
        type Error = VMError;
    
        fn try_from(v: &Value) -> Result<&Tuple, VMError> {
            if let &Value::Tuple(ref tuple) = v { Ok(tuple) } else { Err(VMError::Type) }
        }
    }
    
    impl<'a> TryFrom<&'a Value> for &'a VMBox {
        type Error = VMError;
    
        fn try_from(v: &Value) -> Result<&VMBox, VMError> {
            if let &Value::Box(ref b) = v { Ok(b) } else { Err(VMError::Type) }
        }
    }
    
    impl<'a> TryFrom<&'a Value> for &'a CodePtr {
        type Error = VMError;
    
        fn try_from(v: &Value) -> Result<&CodePtr, VMError> {
            if let &Value::CodePtr(ref f) = v { Ok(f) } else { Err(VMError::Type) }
        }
    }
    
    impl<'a> TryFrom<&'a Value> for &'a Closure {
        type Error = VMError;
    
        fn try_from(v: &Value) -> Result<&Closure, VMError> {
            if let &Value::Cont(ref k) = v { Ok(k) } else { Err(VMError::Type) }
        }
    }
        
    impl<'a> TryFrom<&'a Value> for &'a Record {
        type Error = VMError;
    
        fn try_from(v: &Value) -> Result<&Record, VMError> {
            if let &Value::Record(ref r) = v { Ok(r) } else { Err(VMError::Type) }
        }
    }
}

mod bytecode { /**********************************************************************************/
    use std::marker::PhantomData;

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
    
    impl<T> ParseFields<(DestReg, Atom<T>)> for Instr {
        fn parse(self) -> (DestReg, Atom<T>) {
            (self.reg_arg(0), Atom::from(self.atom_arg(1)))
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
}

mod vm { /*****************************************************************************************/
    use std::convert::TryFrom;
    use gc::Gc;

    use super::{Program, Proc, VMError};
    use value::*;
    use bytecode::*;
        
    #[derive(Debug)]
    pub struct VM {
        regs: Vec<ValueRef>,
        procs: Vec<Gc<Proc>>,
        curr_proc: Gc<Proc>,
        pc: usize
    }
    
    impl VM {
        pub fn new(program: &Program) -> VM {
            let procs = program.procs.clone();
            let curr_proc = program.procs[program.entry].clone();
            VM {
                regs: vec![Gc::new(Value::Null); program.register_demand],
                procs: procs,
                curr_proc: curr_proc,
                pc: 0
            }     
        }
        
        fn fetch(&mut self) -> Result<Instr, VMError> {
            if let Some(&instr) = self.curr_proc.instrs.get(self.pc) {
                self.pc += 1;
                Ok(instr)
            } else {
                Err(VMError::OutOfInstrs)
            }
        }
    
        fn reg(&self, index: AnySrcReg) -> &ValueRef { &self.regs[usize::from(index)] }
        
        fn reg_mut(&mut self, index: DestReg) -> &mut ValueRef { &mut self.regs[usize::from(index)] }

        fn reg_t<'a, T>(&'a self, index: SrcReg<T>) -> Result<T, VMError> where T: TryFrom<&'a Value, Error=VMError> {
            <T as TryFrom<&Value>>::try_from(&**self.reg(AnySrcReg::from(index)))
        }
    
        fn atom(&self, atom: AnyAtom) -> &ValueRef {
            match atom.tag() {
                0 => &self.regs[atom.index()],
                1 => &self.curr_proc.consts[atom.index()],
                _ => unreachable!()     
            }
        }

        fn atom_t<'a, T>(&'a self, atom: Atom<T>) -> Result<T, VMError> where T: TryFrom<&'a Value, Error=VMError> {
            <T as TryFrom<&Value>>::try_from(&**self.atom(AnyAtom::from(atom)))
        }
    
        fn cob(&self, index: ProcIndex) -> &Gc<Proc> { &self.procs[usize::from(index)] }
    
        fn offset_pc(&self, offset: Offset) -> usize {
            (self.pc as isize + isize::from(offset)) as usize     
        }
        
        pub fn run(&mut self) -> Result<ValueRef, VMError> {
            loop {
                let instr = self.fetch()?;
                match instr.op() {
                    MOV => {
                        let (di, v) = {
                            let (di, vi): (DestReg, AnyAtom) = instr.parse();
                            (di, self.atom(vi).clone())
                        };
                        *self.reg_mut(di) = v;
                    },
                
                    IEQ => {
                        let (di, v) = {
                            let (di, ai, bi): (DestReg, Atom<isize>, Atom<isize>) = instr.parse();
                            let a = self.atom_t(ai)?;
                            let b = self.atom_t(bi)?;
                            (di, Gc::new(Value::Bool(a == b)))
                        };
                        *self.reg_mut(di) = v;
                    },
                    ILT => {
                        let (di, v) = {
                            let (di, ai, bi): (DestReg, Atom<isize>, Atom<isize>) = instr.parse();
                            let a = self.atom_t(ai)?;
                            let b = self.atom_t(bi)?;
                            (di, Gc::new(Value::Bool(a < b)))
                        };
                        *self.reg_mut(di) = v;
                    },
                    ILE => {
                        let (di, v) = {
                            let (di, ai, bi): (DestReg, Atom<isize>, Atom<isize>) = instr.parse();
                            let a = self.atom_t(ai)?;
                            let b = self.atom_t(bi)?;
                            (di, Gc::new(Value::Bool(a <= b)))
                        };
                        *self.reg_mut(di) = v;
                    },
                    IGT => {
                        let (di, v) = {
                            let (di, ai, bi): (DestReg, Atom<isize>, Atom<isize>) = instr.parse();
                            let a = self.atom_t(ai)?;
                            let b = self.atom_t(bi)?;
                            (di, Gc::new(Value::Bool(a > b)))
                        };
                        *self.reg_mut(di) = v;
                    },
                    IGE => {
                        let (di, v) = {
                            let (di, ai, bi): (DestReg, Atom<isize>, Atom<isize>) = instr.parse();
                            let a = self.atom_t(ai)?;
                            let b = self.atom_t(bi)?;
                            (di, Gc::new(Value::Bool(a >= b)))
                        };
                        *self.reg_mut(di) = v;
                    },

                    // FIXME: over/underflow, division by zero
                    INEG => {
                        let (di, v) = {
                            let (di, ni): (DestReg, Atom<isize>) = instr.parse();
                            let n = self.atom_t(ni)?;
                            (di, Gc::new(Value::Int(-n)))
                        };
                        *self.reg_mut(di) = v;
                    },
                    IADD => {
                        let (di, v) = {
                            let (di, ai, bi): (DestReg, Atom<isize>, Atom<isize>) = instr.parse();
                            let a = self.atom_t(ai)?;
                            let b = self.atom_t(bi)?;
                            (di, Gc::new(Value::Int(a + b)))
                        };
                        *self.reg_mut(di) = v;
                    },
                    ISUB => {
                        let (di, v) = {
                            let (di, ai, bi): (DestReg, Atom<isize>, Atom<isize>) = instr.parse();
                            let a = self.atom_t(ai)?;
                            let b = self.atom_t(bi)?;
                            (di, Gc::new(Value::Int(a - b)))
                        };
                        *self.reg_mut(di) = v;
                    },
                    IMUL => {
                        let (di, v) = {
                            let (di, ai, bi): (DestReg, Atom<isize>, Atom<isize>) = instr.parse();
                            let a = self.atom_t(ai)?;
                            let b = self.atom_t(bi)?;
                            (di, Gc::new(Value::Int(a * b)))
                        };
                        *self.reg_mut(di) = v;
                    },
                    IDIV => {
                        let (di, v) = {
                            let (di, ai, bi): (DestReg, Atom<isize>, Atom<isize>) = instr.parse();
                            let a = self.atom_t(ai)?;
                            let b = self.atom_t(bi)?;
                            (di, Gc::new(Value::Int(a / b)))
                        };
                        *self.reg_mut(di) = v;
                    },
                    IREM => {
                        let (di, v) = {
                            let (di, ai, bi): (DestReg, Atom<isize>, Atom<isize>) = instr.parse();
                            let a = self.atom_t(ai)?;
                            let b = self.atom_t(bi)?;
                            (di, Gc::new(Value::Int(a % b)))
                        };
                        *self.reg_mut(di) = v;
                    },
                    IMOD => {
                        let (di, v) = {
                            let (di, ai, bi): (DestReg, Atom<isize>, Atom<isize>) = instr.parse();
                            let a = self.atom_t(ai)?;
                            let b = self.atom_t(bi)?;
                            (di, Gc::new(Value::Int((a % b + b) % b)))
                        };
                        *self.reg_mut(di) = v;
                    },
    
                    BOX_NEW => {
                        let di: DestReg = instr.parse();
                        *self.reg_mut(di) = Gc::new(Value::new_box());
                    },
                    BOX_INIT => {
                        let (bi, vi): (SrcReg<&VMBox>, AnyAtom) = instr.parse();
                        let b = self.reg_t(bi)?;
                        let v = self.atom(vi);
                        *b.value.borrow_mut() = v.clone();
                    },
                    BOX_GET => {
                        let (di, bi): (DestReg, Atom<&VMBox>) = instr.parse();
                        let v = {
                            let b = self.atom_t(bi)?;
                            b.value.borrow().clone()
                        };
                        *self.reg_mut(di) = v;
                    },
                    
                    TUPLE_NEW => {
                        let (di, li): (DestReg, Atom<usize>) = instr.parse();
                        let len = self.atom_t(li)?;
                        *self.reg_mut(di) = Gc::new(Value::new_tuple(len));
                    },
                    TUPLE_INIT => {
                        let (ti, ii, vi): (SrcReg<&Tuple>, Atom<usize>, AnyAtom) = instr.parse();
                        let t = self.reg_t(ti)?;
                        let i = self.atom_t(ii)?;
                        let v = self.atom(vi);
                        *t.fields.borrow_mut().get_mut(i).ok_or(VMError::Bounds)? = v.clone();
                    },
                    TUPLE_LEN => {
                        let (di, ti): (DestReg, Atom<&Tuple>) = instr.parse();
                        let len = {
                            let t = self.atom_t(ti)?;
                            Gc::new(Value::Int(t.fields.borrow().len() as isize))
                        };
                        *self.reg_mut(di) = len;
                    },
                    TUPLE_GET => {
                        let (di, ti, ii): (DestReg, Atom<&Tuple>, Atom<usize>) = instr.parse();
                        let v = {
                            let t = self.atom_t(ti)?;
                            let i = self.atom_t(ii)?;
                            t.fields.borrow().get(i).ok_or(VMError::Bounds)?.clone()
                        };
                        *self.reg_mut(di) = v;
                    },
    
                    FN_NEW => {
                        let (di, li): (DestReg, Atom<usize>) = instr.parse();
                        let len = self.atom_t(li)?;
                        *self.reg_mut(di) = Gc::new(Value::new_fn(len));
                    },
                    FN_INIT_CODE => {
                        let (fi, ci): (SrcReg<&Closure>, ProcIndex) = instr.parse();
                        let f = self.reg_t(fi)?;
                        let cob = self.cob(ci).clone();
                        let code = Gc::new(Value::new_code_ptr(cob, 0));
                        *f.code.borrow_mut() = code;
                    },
                    FN_INIT => {
                        let (fi, ii, vi): (SrcReg<&Closure>, Atom<usize>, AnyAtom) = instr.parse();
                        let f = self.reg_t(fi)?;
                        let i = self.atom_t(ii)?;
                        let v = self.atom(vi);
                        *f.env.borrow_mut().get_mut(i).ok_or(VMError::Bounds)? = v.clone();
                    },
                    FN_CODE => {
                        let (di, fi): (DestReg, Atom<&Closure>) = instr.parse();
                        let code = {
                            let f = self.atom_t(fi)?;
                            f.code.borrow().clone()
                        };
                        *self.reg_mut(di) = code;
                    },
                    FN_GET => {
                        let (di, fi, ii): (DestReg, SrcReg<&Closure>, Atom<usize>) = instr.parse();
                        let v = {
                            let f = self.reg_t(fi)?;
                            let i = self.atom_t(ii)?;
                            f.env.borrow().get(i).ok_or(VMError::Bounds)?.clone()
                        };
                        *self.reg_mut(di) = v; 
                    },
                    
                    CONT_NEW => {
                        let (di, li): (DestReg, Atom<usize>) = instr.parse();
                        let len = self.atom_t(li)?;
                        *self.reg_mut(di) = Gc::new(Value::new_cont(len));
                    },
                    CONT_INIT_CODE => {
                        let (ki, offset): (SrcReg<&Closure>, Offset) = instr.parse();
                        let k = self.reg_t(ki)?;
                        let cont_pc = self.offset_pc(offset);
                        let code = Gc::new(Value::new_code_ptr(self.curr_proc.clone(), cont_pc));
                        *k.code.borrow_mut() = code;
                    },
                    CONT_INIT => {
                        let (ki, ii, vi): (SrcReg<&Closure>, Atom<usize>, AnyAtom) = instr.parse();
                        let k = self.reg_t(ki)?;
                        let i = self.atom_t(ii)?;
                        let v = self.atom(vi);
                        *k.env.borrow_mut().get_mut(i).ok_or(VMError::Bounds)? = v.clone();
                    },
                    CONT_CODE => {
                        let (di, ki): (DestReg, Atom<&Closure>) = instr.parse();
                        let code = {
                            let k = self.atom_t(ki)?;
                            k.code.borrow().clone()
                        };
                        *self.reg_mut(di) = code;
                    },
                    CONT_GET => {
                        let (di, ki, ii): (DestReg, SrcReg<&Closure>, Atom<usize>) = instr.parse();
                        let v = {
                            let k = self.reg_t(ki)?;
                            let i = self.atom_t(ii)?;
                            k.env.borrow().get(i).ok_or(VMError::Bounds)?.clone()
                        };
                        *self.reg_mut(di) = v; 
                    },
                    
                    DENV_NEW => {
                        let di: DestReg = instr.parse();
                        *self.reg_mut(di) = Gc::new(Value::new_denv());     
                    },
                    
                    REC_NEW => {
                        let (di, li): (DestReg, Atom<usize>) = instr.parse();
                        let len = self.atom_t(li)?;
                        *self.reg_mut(di) = Gc::new(Value::new_record(len));
                    },
                    REC_INIT_TYPE => {
                        let (ri, ti): (SrcReg<&Record>, AnyAtom) = instr.parse();
                        let r = self.reg_t(ri)?;
                        let t = self.atom(ti).clone();
                        *r.typ.borrow_mut() = t;
                    },
                    REC_INIT => {
                        let (ri, ii, vi): (SrcReg<&Record>, Atom<usize>, AnyAtom) = instr.parse();
                        let r = self.reg_t(ri)?;
                        let i = self.atom_t(ii)?;
                        let v = self.atom(vi);
                        *r.fields.borrow_mut().get_mut(i).ok_or(VMError::Bounds)? = v.clone();
                    },
                    REC_TYPE => {
                        let (di, ri): (DestReg, Atom<&Record>) = instr.parse();
                        let t = {
                            let r = self.atom_t(ri)?;
                            r.typ.borrow().clone()
                        };
                        *self.reg_mut(di) = t;
                    },
                    REC_GET => {
                        let (di, ri, ii): (DestReg, Atom<&Record>, Atom<usize>) = instr.parse();
                        let v = {
                            let r = self.atom_t(ri)?;
                            let i = self.atom_t(ii)?;
                            r.fields.borrow().get(i).ok_or(VMError::Bounds)?.clone()
                        };
                        *self.reg_mut(di) = v;
                    },
                    
                    BRF => {
                        let (ci, offset): (Atom<bool>, Offset) = instr.parse();
                        let cond = self.atom_t(ci)?;
                        if !cond {
                            self.pc = self.offset_pc(offset);
                        }
                    }
    
                    IJMP => {
                        let ci: SrcReg<&CodePtr> = instr.parse();
                        let (cob, pc) = {
                            let code = self.reg_t(ci)?;
                            (code.cob.clone(), code.pc)
                        };
                        self.curr_proc = cob;
                        self.pc = pc; 
                    },
    
                    HALT => {
                        let i: AnyAtom = instr.parse();
                        return Ok(self.atom(i).clone());
                    },
                    
                    op => panic!("unimplemented op {:?}", op)
                }
            }
        }
    }
}

mod deserialize { /*******************************************************************************/
    use std::mem::size_of;
    use std::str::{self, Utf8Error};
    use gc::Gc;

    use super::{Program, Proc};
    use value::{Value, ValueRef};
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
}

/* Main *******************************************************************************************/

use std::io::{self, Read};
use std::fs::File;
use clap::{App, Arg};

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
