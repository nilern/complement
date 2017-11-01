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

    fn load_atom(&self, atom: Atom) -> &ValueRef {
        match atom.tag() {
            0 => &self.regs[atom.index()],
            1 => &self.curr_proc.consts[atom.index()],
            _ => unreachable!()     
        }
    }

    pub fn run(&mut self) -> Result<ValueRef, VMError> {
        loop {
            let instr = self.fetch()?;
            match instr.op() {
                MOV => {
                    let (di, vi): (u8, Atom) = instr.parse();
                    let v = self.load_atom(vi).clone();
                    self.regs[di as usize] = v;
                },
            
                IEQ => {
                    let (di, ai, bi): (u8, Atom, Atom) = instr.parse();
                    let a = isize::try_from(&**self.load_atom(ai))?;
                    let b = isize::try_from(&**self.load_atom(bi))?;
                    self.regs[di as usize] = Gc::new(Value::Bool(a == b));
                },
                IADD => {
                    let (di, ai, bi): (u8, Atom, Atom) = instr.parse();
                    let a = isize::try_from(&**self.load_atom(ai))?;
                    let b = isize::try_from(&**self.load_atom(bi))?;
                    self.regs[di as usize] = Gc::new(Value::Int(a + b));
                },
                ISUB => {
                    let (di, ai, bi): (u8, Atom, Atom) = instr.parse();
                    let a = isize::try_from(&**self.load_atom(ai))?;
                    let b = isize::try_from(&**self.load_atom(bi))?;
                    self.regs[di as usize] = Gc::new(Value::Int(a - b));
                },
                IMUL => {
                    let (di, ai, bi): (u8, Atom, Atom) = instr.parse();
                    let a = isize::try_from(&**self.load_atom(ai))?;
                    let b = isize::try_from(&**self.load_atom(bi))?;
                    self.regs[di as usize] = Gc::new(Value::Int(a * b));
                },

                BOX_NEW => {
                    let di: u8 = instr.parse();
                    self.regs[di as usize] = Gc::new(Value::new_box());
                },
                BOX_INIT => {
                    let (bi, vi): (u8, Atom) = instr.parse();
                    let b: &VMBox = TryFrom::try_from(&*self.regs[bi as usize])?;
                    let v = self.load_atom(vi);
                    *b.value.borrow_mut() = v.clone();
                },
                BOX_GET => {
                    let (di, bi): (u8, Atom) = instr.parse();
                    let v = {
                        let b: &VMBox = TryFrom::try_from(&**self.load_atom(bi))?;
                        b.value.borrow().clone()
                    };
                    self.regs[di as usize] = v;
                },
                
                TUPLE_NEW => {
                    let (di, li): (u8, Atom) = instr.parse();
                    let len = isize::try_from(&**self.load_atom(li))? as usize;
                    self.regs[di as usize] = Gc::new(Value::new_tuple(len));
                },
                TUPLE_INIT => {
                    let (ti, ii, vi): (u8, Atom, Atom) = instr.parse();
                    let t: &Tuple = TryFrom::try_from(&*self.regs[ti as usize])?;
                    let i = usize::try_from(&**self.load_atom(ii))?;
                    let v = self.load_atom(vi);
                    *t.fields.borrow_mut().get_mut(i).ok_or(VMError::Bounds)? = v.clone();
                },
                TUPLE_LEN => {
                    let (di, ti): (u8, Atom) = instr.parse();
                    let len = {
                        let t: &Tuple = TryFrom::try_from(&**self.load_atom(ti))?;
                        Gc::new(Value::Int(t.fields.borrow().len() as isize))
                    };
                    self.regs[di as usize] = len;
                },
                TUPLE_GET => {
                    let (di, ti, ii): (u8, Atom, Atom) = instr.parse();
                    let v = {
                        let t: &Tuple = TryFrom::try_from(&**self.load_atom(ti))?;
                        let i = usize::try_from(&**self.load_atom(ii))?;
                        t.fields.borrow().get(i).ok_or(VMError::Bounds)?.clone()
                    };
                    self.regs[di as usize] = v;
                },

                FN_NEW => {
                    let (di, li): (u8, Atom) = instr.parse();
                    let len = usize::try_from(&**self.load_atom(li))?;
                    self.regs[di as usize] = Gc::new(Value::new_fn(len));
                },
                FN_INIT_CODE => {
                    let (fi, ci): (u8, u16) = instr.parse();
                    let f: &Closure = TryFrom::try_from(&*self.regs[fi as usize])?;
                    let cob = self.procs[ci as usize].clone();
                    let code = Gc::new(Value::new_code_ptr(cob, 0));
                    *f.code.borrow_mut() = code;
                },
                FN_INIT => {
                    let (fi, ii, vi): (u8, Atom, Atom) = instr.parse();
                    let f: &Closure = TryFrom::try_from(&*self.regs[fi as usize])?;
                    let i = usize::try_from(&**self.load_atom(ii))?;
                    let v = self.load_atom(vi);
                    *f.env.borrow_mut().get_mut(i).ok_or(VMError::Bounds)? = v.clone();
                },
                FN_CODE => {
                    let (di, fi): (u8, Atom) = instr.parse();
                    let code = {
                        let f: &Closure = TryFrom::try_from(&**self.load_atom(fi))?;
                        f.code.borrow().clone()
                    };
                    self.regs[di as usize] = code;
                },
                FN_GET => {
                    let (di, fi, ii): (u8, u8, Atom) = instr.parse();
                    let v = {
                        let f: &Closure = TryFrom::try_from(&*self.regs[fi as usize])?;
                        let i = usize::try_from(&**self.load_atom(ii))?;
                        f.env.borrow().get(i).ok_or(VMError::Bounds)?.clone()
                    };
                    self.regs[di as usize] = v; 
                },
                
                CONT_NEW => {
                    let (di, li): (u8, Atom) = instr.parse();
                    let len = usize::try_from(&**self.load_atom(li))?;
                    self.regs[di as usize] = Gc::new(Value::new_cont(len));
                },
                CONT_INIT_CODE => {
                    let (ki, offset): (u8, i16) = instr.parse();
                    let k: &Closure = TryFrom::try_from(&*self.regs[ki as usize])?;
                    let cont_pc = (self.pc as isize + offset as isize) as usize;
                    let code = Gc::new(Value::new_code_ptr(self.curr_proc.clone(), cont_pc));
                    *k.code.borrow_mut() = code;
                },
                CONT_INIT => {
                    let (ki, ii, vi): (u8, Atom, Atom) = instr.parse();
                    let k: &Closure = TryFrom::try_from(&*self.regs[ki as usize])?;
                    let i = usize::try_from(&**self.load_atom(ii))?;
                    let v = self.load_atom(vi);
                    *k.env.borrow_mut().get_mut(i).ok_or(VMError::Bounds)? = v.clone();
                },
                CONT_CODE => {
                    let (di, ki): (u8, Atom) = instr.parse();
                    let code = {
                        let k: &Closure = TryFrom::try_from(&**self.load_atom(ki))?;
                        k.code.borrow().clone()
                    };
                    self.regs[di as usize] = code;
                },
                CONT_GET => {
                    let (di, ki, ii): (u8, u8, Atom) = instr.parse();
                    let v = {
                        let k: &Closure = TryFrom::try_from(&*self.regs[ki as usize])?;
                        let i = usize::try_from(&**self.load_atom(ii))?;
                        k.env.borrow().get(i).ok_or(VMError::Bounds)?.clone()
                    };
                    self.regs[di as usize] = v; 
                },
                
                DENV_NEW => {
                    let di: u8 = instr.parse();
                    self.regs[di as usize] = Gc::new(Value::new_denv());     
                },

                BRF => {
                    let (ci, offset): (Atom, i16) = instr.parse();
                    let cond = bool::try_from(&**self.load_atom(ci))?;
                    if !cond {
                        self.pc = (self.pc as isize + offset as isize) as usize;
                    }  
                }

                IJMP => {
                    let ci: u8 = instr.parse();
                    let code: &CodePtr = TryFrom::try_from(&*self.regs[ci as usize])?;
                    self.curr_proc = code.cob.clone();
                    self.pc = code.pc; 
                },

                HALT => {
                    let i: Atom = instr.parse();
                    return Ok(self.load_atom(i).clone());
                },
                
                op => panic!("unimplemented op {:?}", op)
            }
        }
    }
}
