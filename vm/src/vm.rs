use std::convert::TryFrom;
use gc::Gc;

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
