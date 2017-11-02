#![feature(try_from)]

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
    pub enum Value {
        Int(isize),
        Bool(bool),
        
        Symbol(String),
    
        Tuple(Tuple),
    
        Null,
        Box(VMBox),
        
        CodePtr(CodePtr),
        Fn(Closure),
        Cont(Closure),
        
        Denv(HashMap<String, ValueRef>)
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
}

mod bytecode { /**********************************************************************************/
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
    
    impl From<Reg> for usize {
        fn from(reg: Reg) -> usize { reg.0 as usize }
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
            let shift = 8 * (index + 1);
            (self.0 >> shift) & BYTE_MASK
        }
    
        fn u8_arg(self, index: usize) -> u8 { self.byte_arg(index) as u8 }
    
        fn reg_arg(self, index: usize) -> Reg { Reg(self.u8_arg(index)) }
        
        fn atom_arg(self, index: usize) -> Atom { Atom(self.u8_arg(index)) }
            
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
    
        fn reg(&self, index: Reg) -> &ValueRef { &self.regs[usize::from(index)] }
        
        fn reg_mut(&mut self, index: Reg) -> &mut ValueRef { &mut self.regs[usize::from(index)] }
    
        fn atom(&self, atom: Atom) -> &ValueRef {
            match atom.tag() {
                0 => &self.regs[atom.index()],
                1 => &self.curr_proc.consts[atom.index()],
                _ => unreachable!()     
            }
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
                        let (di, vi): (Reg, Atom) = instr.parse();
                        let v = self.atom(vi).clone();
                        *self.reg_mut(di) = v;
                    },
                
                    IEQ => {
                        let (di, ai, bi): (Reg, Atom, Atom) = instr.parse();
                        let a = isize::try_from(&**self.atom(ai))?;
                        let b = isize::try_from(&**self.atom(bi))?;
                        *self.reg_mut(di) = Gc::new(Value::Bool(a == b));
                    },
                    IADD => {
                        let (di, ai, bi): (Reg, Atom, Atom) = instr.parse();
                        let a = isize::try_from(&**self.atom(ai))?;
                        let b = isize::try_from(&**self.atom(bi))?;
                        *self.reg_mut(di) = Gc::new(Value::Int(a + b));
                    },
                    ISUB => {
                        let (di, ai, bi): (Reg, Atom, Atom) = instr.parse();
                        let a = isize::try_from(&**self.atom(ai))?;
                        let b = isize::try_from(&**self.atom(bi))?;
                        *self.reg_mut(di) = Gc::new(Value::Int(a - b));
                    },
                    IMUL => {
                        let (di, ai, bi): (Reg, Atom, Atom) = instr.parse();
                        let a = isize::try_from(&**self.atom(ai))?;
                        let b = isize::try_from(&**self.atom(bi))?;
                        *self.reg_mut(di) = Gc::new(Value::Int(a * b));
                    },
    
                    BOX_NEW => {
                        let di: Reg = instr.parse();
                        *self.reg_mut(di) = Gc::new(Value::new_box());
                    },
                    BOX_INIT => {
                        let (bi, vi): (Reg, Atom) = instr.parse();
                        let b: &VMBox = TryFrom::try_from(&**self.reg(bi))?;
                        let v = self.atom(vi);
                        *b.value.borrow_mut() = v.clone();
                    },
                    BOX_GET => {
                        let (di, bi): (Reg, Atom) = instr.parse();
                        let v = {
                            let b: &VMBox = TryFrom::try_from(&**self.atom(bi))?;
                            b.value.borrow().clone()
                        };
                        *self.reg_mut(di) = v;
                    },
                    
                    TUPLE_NEW => {
                        let (di, li): (Reg, Atom) = instr.parse();
                        let len = usize::try_from(&**self.atom(li))?;
                        *self.reg_mut(di) = Gc::new(Value::new_tuple(len));
                    },
                    TUPLE_INIT => {
                        let (ti, ii, vi): (Reg, Atom, Atom) = instr.parse();
                        let t: &Tuple = TryFrom::try_from(&**self.reg(ti))?;
                        let i = usize::try_from(&**self.atom(ii))?;
                        let v = self.atom(vi);
                        *t.fields.borrow_mut().get_mut(i).ok_or(VMError::Bounds)? = v.clone();
                    },
                    TUPLE_LEN => {
                        let (di, ti): (Reg, Atom) = instr.parse();
                        let len = {
                            let t: &Tuple = TryFrom::try_from(&**self.atom(ti))?;
                            Gc::new(Value::Int(t.fields.borrow().len() as isize))
                        };
                        *self.reg_mut(di) = len;
                    },
                    TUPLE_GET => {
                        let (di, ti, ii): (Reg, Atom, Atom) = instr.parse();
                        let v = {
                            let t: &Tuple = TryFrom::try_from(&**self.atom(ti))?;
                            let i = usize::try_from(&**self.atom(ii))?;
                            t.fields.borrow().get(i).ok_or(VMError::Bounds)?.clone()
                        };
                        *self.reg_mut(di) = v;
                    },
    
                    FN_NEW => {
                        let (di, li): (Reg, Atom) = instr.parse();
                        let len = usize::try_from(&**self.atom(li))?;
                        *self.reg_mut(di) = Gc::new(Value::new_fn(len));
                    },
                    FN_INIT_CODE => {
                        let (fi, ci): (Reg, ProcIndex) = instr.parse();
                        let f: &Closure = TryFrom::try_from(&**self.reg(fi))?;
                        let cob = self.cob(ci).clone();
                        let code = Gc::new(Value::new_code_ptr(cob, 0));
                        *f.code.borrow_mut() = code;
                    },
                    FN_INIT => {
                        let (fi, ii, vi): (Reg, Atom, Atom) = instr.parse();
                        let f: &Closure = TryFrom::try_from(&**self.reg(fi))?;
                        let i = usize::try_from(&**self.atom(ii))?;
                        let v = self.atom(vi);
                        *f.env.borrow_mut().get_mut(i).ok_or(VMError::Bounds)? = v.clone();
                    },
                    FN_CODE => {
                        let (di, fi): (Reg, Atom) = instr.parse();
                        let code = {
                            let f: &Closure = TryFrom::try_from(&**self.atom(fi))?;
                            f.code.borrow().clone()
                        };
                        *self.reg_mut(di) = code;
                    },
                    FN_GET => {
                        let (di, fi, ii): (Reg, Reg, Atom) = instr.parse();
                        let v = {
                            let f: &Closure = TryFrom::try_from(&**self.reg(fi))?;
                            let i = usize::try_from(&**self.atom(ii))?;
                            f.env.borrow().get(i).ok_or(VMError::Bounds)?.clone()
                        };
                        *self.reg_mut(di) = v; 
                    },
                    
                    CONT_NEW => {
                        let (di, li): (Reg, Atom) = instr.parse();
                        let len = usize::try_from(&**self.atom(li))?;
                        *self.reg_mut(di) = Gc::new(Value::new_cont(len));
                    },
                    CONT_INIT_CODE => {
                        let (ki, offset): (Reg, Offset) = instr.parse();
                        let k: &Closure = TryFrom::try_from(&**self.reg(ki))?;
                        let cont_pc = self.offset_pc(offset);
                        let code = Gc::new(Value::new_code_ptr(self.curr_proc.clone(), cont_pc));
                        *k.code.borrow_mut() = code;
                    },
                    CONT_INIT => {
                        let (ki, ii, vi): (Reg, Atom, Atom) = instr.parse();
                        let k: &Closure = TryFrom::try_from(&**self.reg(ki))?;
                        let i = usize::try_from(&**self.atom(ii))?;
                        let v = self.atom(vi);
                        *k.env.borrow_mut().get_mut(i).ok_or(VMError::Bounds)? = v.clone();
                    },
                    CONT_CODE => {
                        let (di, ki): (Reg, Atom) = instr.parse();
                        let code = {
                            let k: &Closure = TryFrom::try_from(&**self.atom(ki))?;
                            k.code.borrow().clone()
                        };
                        *self.reg_mut(di) = code;
                    },
                    CONT_GET => {
                        let (di, ki, ii): (Reg, Reg, Atom) = instr.parse();
                        let v = {
                            let k: &Closure = TryFrom::try_from(&**self.reg(ki))?;
                            let i = usize::try_from(&**self.atom(ii))?;
                            k.env.borrow().get(i).ok_or(VMError::Bounds)?.clone()
                        };
                        *self.reg_mut(di) = v; 
                    },
                    
                    DENV_NEW => {
                        let di: Reg = instr.parse();
                        *self.reg_mut(di) = Gc::new(Value::new_denv());     
                    },
    
                    BRF => {
                        let (ci, offset): (Atom, Offset) = instr.parse();
                        let cond = bool::try_from(&**self.atom(ci))?;
                        if !cond {
                            self.pc = self.offset_pc(offset);
                        }  
                    }
    
                    IJMP => {
                        let ci: Reg = instr.parse();
                        let (cob, pc) = {
                            let code: &CodePtr = TryFrom::try_from(&**self.reg(ci))?;
                            (code.cob.clone(), code.pc)
                        };
                        self.curr_proc = cob;
                        self.pc = pc; 
                    },
    
                    HALT => {
                        let i: Atom = instr.parse();
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
            1 => parse_string(input).map(|s| Gc::new(Value::Symbol(s))),
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
