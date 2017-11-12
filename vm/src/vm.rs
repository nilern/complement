use std::convert::TryFrom;
use gc::Gc;

use code::*;
use data::{VMError, Program, VMBox, Tuple, Record, Proc, Closure, CodePtr, Value, ValueRef};

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
