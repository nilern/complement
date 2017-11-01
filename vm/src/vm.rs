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

    fn load_atom(&self, (tag, index): (u8, u8)) -> &ValueRef {
        match tag {
            0 => &self.regs[index as usize],
            1 => &self.curr_proc.consts[index as usize],
            _ => unreachable!()     
        }
    }

    pub fn run(&mut self) -> Result<ValueRef, VMError> {
        loop {
            let instr = self.fetch()?;
            match instr.op() {
                MOV => {
                    let di = instr.byte_arg(0);
                    let v = self.load_atom(instr.atom_arg(1)).clone();
                    self.regs[di] = v;
                },
            
                IEQ => {
                    let di = instr.byte_arg(0);
                    let a = isize::try_from(&**self.load_atom(instr.atom_arg(1)))?;
                    let b = isize::try_from(&**self.load_atom(instr.atom_arg(2)))?;
                    self.regs[di] = Gc::new(Value::Bool(a == b));
                },
                IADD => {
                    let di = instr.byte_arg(0);
                    let a = isize::try_from(&**self.load_atom(instr.atom_arg(1)))?;
                    let b = isize::try_from(&**self.load_atom(instr.atom_arg(2)))?;
                    self.regs[di] = Gc::new(Value::Int(a + b));
                },
                ISUB => {
                    let di = instr.byte_arg(0);
                    let a = isize::try_from(&**self.load_atom(instr.atom_arg(1)))?;
                    let b = isize::try_from(&**self.load_atom(instr.atom_arg(2)))?;
                    self.regs[di] = Gc::new(Value::Int(a - b));
                },
                IMUL => {
                    let di = instr.byte_arg(0);
                    let a = isize::try_from(&**self.load_atom(instr.atom_arg(1)))?;
                    let b = isize::try_from(&**self.load_atom(instr.atom_arg(2)))?;
                    self.regs[di] = Gc::new(Value::Int(a * b));
                },

                BOX_NEW => {
                    let di = instr.byte_arg(0);
                    self.regs[di] = Gc::new(Value::new_box());
                },
                BOX_INIT => {
                    let b: &VMBox = TryFrom::try_from(&*self.regs[instr.byte_arg(0)])?;
                    let v = self.load_atom(instr.atom_arg(1));
                    *b.value.borrow_mut() = v.clone();
                },
                BOX_GET => {
                    let di = instr.byte_arg(0);
                    let v = {
                        let b: &VMBox = TryFrom::try_from(&**self.load_atom(instr.atom_arg(1)))?;
                        b.value.borrow().clone()
                    };
                    self.regs[di] = v;
                },
                
                TUPLE_NEW => {
                    let di = instr.byte_arg(0);
                    let len = isize::try_from(&**self.load_atom(instr.atom_arg(1)))? as usize;
                    self.regs[di] = Gc::new(Value::new_tuple(len));
                },
                TUPLE_INIT => {
                    let t: &Tuple = TryFrom::try_from(&*self.regs[instr.byte_arg(0)])?;
                    let i = usize::try_from(&**self.load_atom(instr.atom_arg(1)))?;
                    let v = self.load_atom(instr.atom_arg(2));
                    *t.fields.borrow_mut().get_mut(i).ok_or(VMError::Bounds)? = v.clone();
                },
                TUPLE_LEN => {
                    let di = instr.byte_arg(0);
                    let len = {
                        let t: &Tuple = TryFrom::try_from(&**self.load_atom(instr.atom_arg(1)))?;
                        Gc::new(Value::Int(t.fields.borrow().len() as isize))
                    };
                    self.regs[di] = len;
                },
                TUPLE_GET => {
                    let di = instr.byte_arg(0);
                    let v = {
                        let t: &Tuple = TryFrom::try_from(&**self.load_atom(instr.atom_arg(1)))?;
                        let i = usize::try_from(&**self.load_atom(instr.atom_arg(2)))?;
                        t.fields.borrow().get(i).ok_or(VMError::Bounds)?.clone()
                    };
                    self.regs[di] = v;
                },

                FN_NEW => {
                    let di = instr.byte_arg(0);
                    let len = usize::try_from(&**self.load_atom(instr.atom_arg(1)))?;
                    self.regs[di] = Gc::new(Value::new_fn(len));
                },
                FN_INIT_CODE => {
                    let f: &VMFn = TryFrom::try_from(&*self.regs[instr.byte_arg(0)])?;
                    let cob = &self.procs[instr.short_arg()];
                    *f.code.borrow_mut() = Some(cob.clone());
                },
                FN_INIT => {
                    let f: &VMFn = TryFrom::try_from(&*self.regs[instr.byte_arg(0)])?;
                    let i = usize::try_from(&**self.load_atom(instr.atom_arg(1)))?;
                    let v = self.load_atom(instr.atom_arg(2));
                    *f.env.borrow_mut().get_mut(i).ok_or(VMError::Bounds)? = v.clone();
                },
                FN_CODE => {
                    let di = instr.byte_arg(0);
                    let code = {
                        let f: &VMFn = TryFrom::try_from(&**self.load_atom(instr.atom_arg(1)))?;
                        if let &Some(ref cob) = &*f.code.borrow() {
                            Gc::new(Value::new_code_ptr(cob.clone(), 0))
                        } else {
                            return Err(VMError::Uninitialized);
                        }
                    };
                    self.regs[di] = code;
                },
                FN_GET => {
                    let di = instr.byte_arg(0);
                    let v = {
                        let f: &VMFn = TryFrom::try_from(&*self.regs[instr.byte_arg(1)])?;
                        let i = usize::try_from(&**self.load_atom(instr.atom_arg(2)))?;
                        f.env.borrow().get(i).ok_or(VMError::Bounds)?.clone()
                    };
                    self.regs[di] = v;
                },
                
                CONT_NEW => {
                    let di = instr.byte_arg(0);
                    let len = usize::try_from(&**self.load_atom(instr.atom_arg(1)))?;
                    self.regs[di] = Gc::new(Value::new_cont(len));
                },
                CONT_INIT_CODE => {
                    let k: &Cont = TryFrom::try_from(&*self.regs[instr.byte_arg(0)])?;
                    let offset = instr.short_arg() as isize;
                    let cont_pc = (self.pc as isize + offset) as usize;
                    let code = Gc::new(Value::new_code_ptr(self.curr_proc.clone(), cont_pc));
                    *k.code.borrow_mut() = code;
                },
                CONT_INIT => {
                    let k: &Cont = TryFrom::try_from(&*self.regs[instr.byte_arg(0)])?;
                    let i = usize::try_from(&**self.load_atom(instr.atom_arg(1)))?;
                    let v = self.load_atom(instr.atom_arg(2));
                    *k.env.borrow_mut().get_mut(i).ok_or(VMError::Bounds)? = v.clone();
                },
                CONT_CODE => {
                    let di = instr.byte_arg(0);
                    let code = {
                        let k: &Cont = TryFrom::try_from(&**self.load_atom(instr.atom_arg(1)))?;
                        k.code.borrow().clone()
                    };
                    self.regs[di] = code;
                },
                CONT_GET => {
                    let di = instr.byte_arg(0);
                    let v = {
                        let k: &Cont = TryFrom::try_from(&*self.regs[instr.byte_arg(1)])?;
                        let i = usize::try_from(&**self.load_atom(instr.atom_arg(2)))?;
                        k.env.borrow().get(i).ok_or(VMError::Bounds)?.clone()
                    };
                    self.regs[di] = v; 
                },
                
                DENV_NEW => {
                    let di = instr.byte_arg(0);
                    self.regs[di] = Gc::new(Value::new_denv());     
                },

                BRF => {
                    let cond = bool::try_from(&**self.load_atom(instr.atom_arg(0)))?;
                    if !cond {
                        let offset = instr.short_arg() as isize;
                        self.pc = (self.pc as isize + offset) as usize;
                    }  
                }

                IJMP => {
                    let code: &CodePtr = TryFrom::try_from(&*self.regs[instr.byte_arg(0)])?;
                    self.curr_proc = code.cob.clone();
                    self.pc = code.pc; 
                },

                HALT => return Ok(self.load_atom(instr.atom_arg(0)).clone()),
                
                op => panic!("unimplemented op {:?}", op)
            }
        }
    }
}
