use std::convert::TryFrom;
use gc::Gc;

use value::{Program, Proc, Value, ValueRef};
use bytecode::*;

#[derive(Debug)]
pub enum VMError {
    OutOfInstrs,
    Uninitialized,
    Type
}

impl<'a> TryFrom<&'a Value> for isize {
    type Error = VMError;

    fn try_from(v: &Value) -> Result<isize, VMError> {
        if let &Value::Int(i) = v {
            Ok(i)
        } else {
            Err(VMError::Type) 
        }     
    }
}

impl<'a> TryFrom<&'a Value> for usize {
    type Error = VMError;

    fn try_from(v: &Value) -> Result<usize, VMError> {
        if let &Value::Int(i) = v {
            Ok(i as usize)
        } else {
            Err(VMError::Type) 
        }     
    }
}

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
    
    fn consts(&self) -> &[ValueRef] { self.curr_proc.consts.as_slice() }

    fn instrs(&self) -> &[Instr] { self.curr_proc.instrs.as_slice() }

    fn atom(&self, ai: Atom) -> ValueRef {
        match ai {
            Atom::Reg(ri) => self.regs[ri].clone(),
            Atom::Const(ci) => self.consts()[ci].clone()   
        }
    }

    pub fn run(&mut self) -> Result<ValueRef, VMError> {
        while self.pc < self.instrs().len() {
            let instr = self.instrs()[self.pc];
            self.pc += 1;
            match instr.op() {
                MOV => {
                    let di = instr.byte_arg(0);
                    let v = self.atom(instr.atom_arg(1));
                    self.regs[di] = v;
                },
            
                IEQ => {
                    let di = instr.byte_arg(0);
                    let a = isize::try_from(&*self.atom(instr.atom_arg(1)))?;
                    let b = isize::try_from(&*self.atom(instr.atom_arg(2)))?;
                    self.regs[di] = Gc::new(Value::Bool(a == b));
                },
                IADD => {
                    let di = instr.byte_arg(0);
                    let a = isize::try_from(&*self.atom(instr.atom_arg(1)))?;
                    let b = isize::try_from(&*self.atom(instr.atom_arg(2)))?;
                    self.regs[di] = Gc::new(Value::Int(a + b));
                },
                ISUB => {
                    let di = instr.byte_arg(0);
                    let a = isize::try_from(&*self.atom(instr.atom_arg(1)))?;
                    let b = isize::try_from(&*self.atom(instr.atom_arg(2)))?;
                    self.regs[di] = Gc::new(Value::Int(a - b));
                },
                IMUL => {
                    let di = instr.byte_arg(0);
                    let a = isize::try_from(&*self.atom(instr.atom_arg(1)))?;
                    let b = isize::try_from(&*self.atom(instr.atom_arg(2)))?;
                    self.regs[di] = Gc::new(Value::Int(a * b));
                },

                BOX_NEW => {
                    let di = instr.byte_arg(0);
                    self.regs[di] = Gc::new(Value::new_box());
                },
                BOX_INIT => {
                    let b = &self.regs[instr.byte_arg(0)];
                    let v = self.atom(instr.atom_arg(1));
                    if let &Value::Box(ref cell) = &**b {
                        *cell.borrow_mut() = v;
                    } else {
                        return Err(VMError::Type);     
                    }
                },
                BOX_GET => {
                    let di = instr.byte_arg(0);
                    let b = &self.atom(instr.atom_arg(1));
                    if let &Value::Box(ref cell) = &**b {
                        self.regs[di] = cell.borrow().clone();
                    } else {
                        return Err(VMError::Type);     
                    }
                },
                
                TUPLE_NEW => {
                    let di = instr.byte_arg(0);
                    let len = isize::try_from(&*self.atom(instr.atom_arg(1)))? as usize;
                    self.regs[di] = Gc::new(Value::new_tuple(len));
                },
                TUPLE_INIT => {
                    let f = &self.regs[instr.byte_arg(0)];
                    let i = usize::try_from(&*self.atom(instr.atom_arg(1)))?;
                    let v = self.atom(instr.atom_arg(2)).clone();
                    if let &Value::Tuple(ref fields_cell) = &**f {
                        fields_cell.borrow_mut()[i] = v;
                    } else {
                        return Err(VMError::Type);     
                    }
                },
                TUPLE_LEN => {
                    let di = instr.byte_arg(0);
                    let t = self.atom(instr.atom_arg(1)).clone();
                    if let &Value::Tuple(ref fields_cell) = &*t {
                        self.regs[di] = Gc::new(Value::Int(fields_cell.borrow().len() as isize));
                    } else {
                        return Err(VMError::Type);     
                    }
                },
                TUPLE_GET => {
                    let di = instr.byte_arg(0);
                    let t = self.atom(instr.atom_arg(1)).clone();
                    let i = usize::try_from(&*self.atom(instr.atom_arg(2)))?;
                    if let &Value::Tuple(ref fields_cell) = &*t {
                        self.regs[di] = fields_cell.borrow()[i].clone();
                    } else {
                        return Err(VMError::Type);     
                    }
                },

                FN_NEW => {
                    let di = instr.byte_arg(0);
                    let len = isize::try_from(&*self.atom(instr.atom_arg(1)))? as usize;
                    self.regs[di] = Gc::new(Value::new_fn(len));
                },
                FN_INIT_CODE => {
                    let f = &self.regs[instr.byte_arg(0)];
                    let cob = self.procs[instr.short_arg()].clone();
                    if let &Value::Fn(ref proc_cell, _) = &**f {
                        *proc_cell.borrow_mut() = Some(cob);
                    } else {
                        return Err(VMError::Type);     
                    }
                },
                FN_INIT => {
                    let f = &self.regs[instr.byte_arg(0)];
                    let i = usize::try_from(&*self.atom(instr.atom_arg(1)))?;
                    let v = self.atom(instr.atom_arg(2));
                    if let &Value::Fn(_, ref env_cell) = &**f {
                        env_cell.borrow_mut()[i] = v;
                    } else {
                        return Err(VMError::Type);     
                    }
                },
                FN_CODE => {
                    let di = instr.byte_arg(0);
                    let f = self.atom(instr.atom_arg(1));
                    if let &Value::Fn(ref proc_cell, _) = &*f {
                        if let &Some(ref cob) = &*proc_cell.borrow() {
                            self.regs[di] = Gc::new(Value::CodePtr(cob.clone(), 0));
                        } else {
                            return Err(VMError::Uninitialized);
                        }
                    } else {
                        return Err(VMError::Type);     
                    }
                },
                FN_GET => {
                    let di = instr.byte_arg(0);
                    let f = self.regs[instr.byte_arg(1)].clone();
                    let i = usize::try_from(&*self.atom(instr.atom_arg(2)))?;
                    if let &Value::Fn(_, ref env_cell) = &*f {
                        self.regs[di] = env_cell.borrow()[i].clone();
                    } else {
                        return Err(VMError::Type);     
                    }
                },
                
                CONT_NEW => {
                    let di = instr.byte_arg(0);
                    let len = isize::try_from(&*self.atom(instr.atom_arg(1)))? as usize;
                    self.regs[di] = Gc::new(Value::new_cont(len));
                },
                CONT_INIT_CODE => {
                    let f = &self.regs[instr.byte_arg(0)];
                    let offset = instr.short_arg() as isize;
                    if let &Value::Cont(ref code_cell, _) = &**f {
                        let cont_pc = (self.pc as isize + offset) as usize;
                        let code = Gc::new(Value::CodePtr(self.curr_proc.clone(), cont_pc));
                        *code_cell.borrow_mut() = code;
                    } else {
                        return Err(VMError::Type);     
                    }
                },
                CONT_INIT => {
                    let k = &self.regs[instr.byte_arg(0)];
                    let i = usize::try_from(&*self.atom(instr.atom_arg(1)))?;
                    let v = self.atom(instr.atom_arg(2));
                    if let &Value::Cont(_, ref env_cell) = &**k {
                        env_cell.borrow_mut()[i] = v;
                    } else {
                        return Err(VMError::Type);     
                    }
                },
                CONT_CODE => {
                    let di = instr.byte_arg(0);
                    let k = self.atom(instr.atom_arg(1));
                    if let &Value::Cont(ref code_cell, _) = &*k {
                        if let &Value::CodePtr(ref cob, ref pc) = &**code_cell.borrow() {
                            self.regs[di] = Gc::new(Value::CodePtr(cob.clone(), *pc));
                        } else {
                            return Err(VMError::Uninitialized);
                        }
                    } else {
                        return Err(VMError::Type);     
                    }
                },
                CONT_GET => {
                    let di = instr.byte_arg(0);
                    let k = self.regs[instr.byte_arg(1)].clone();
                    let i = usize::try_from(&*self.atom(instr.atom_arg(2)))?;
                    if let &Value::Cont(_, ref env_cell) = &*k {
                        self.regs[di] = env_cell.borrow()[i].clone();
                    } else {
                        return Err(VMError::Type);     
                    }
                },
                
                DENV_NEW => {
                    let di = instr.byte_arg(0);
                    self.regs[di] = Gc::new(Value::new_denv());     
                },

                BRF => {
                    let cond = self.atom(instr.atom_arg(0));
                    match &*cond {
                        &Value::Bool(true) => {},
                        &Value::Bool(false) => {
                            let offset = instr.short_arg() as isize;
                            self.pc = (self.pc as isize + offset) as usize;  
                        },
                        _ => return Err(VMError::Type)
                    }     
                }

                IJMP => {
                    let code = &self.regs[instr.byte_arg(0)];
                    if let &Value::CodePtr(ref cob, ref pc) = &**code {
                        self.curr_proc = cob.clone();
                        self.pc = *pc;
                    } else {
                        return Err(VMError::Type);     
                    }  
                },

                HALT => return Ok(self.atom(instr.atom_arg(0))),
                
                op => panic!("unimplemented op {:?}", op)
            }
        }
        Err(VMError::OutOfInstrs)
    }
}
