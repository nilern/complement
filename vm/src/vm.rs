use std::convert::TryFrom;
use std::slice;
use gc::Gc;
use libloading::Library;
use libffi::middle::{Cif, Type, Arg, FfiAbi};

use code::*;
use data::{VMError, Program, Tuple, Proc, Closure, CodePtr, Value, ValueRef,
           as_ffi_type, as_arg, inject};

// FIXME: Not safe-for-space since ValueRef:s are just left in registers until the register is
//        reused. It is probably prudent to address that when we replace rust-gc and implement
//        safepoints. With rust-gc we would need the compiler to encode liveness information and
//        then have the VM read that all the time so that it can clear registers as they die, which
//        would be compilcated and slow.

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
        use code::InstrView::*;
    
        loop {
            match self.fetch()?.decode() {
                Mov { dest, src } => {
                    *self.reg_mut(dest) = self.atom(src).clone();
                },
                
                IEq { dest, arg1, arg2 } => {
                    *self.reg_mut(dest) =
                        Gc::new(Value::Bool(self.atom_t(arg1)? == self.atom_t(arg2)?));
                },
                ILt { dest, arg1, arg2 } => {
                    *self.reg_mut(dest) =
                        Gc::new(Value::Bool(self.atom_t(arg1)? < self.atom_t(arg2)?));
                },
                ILe { dest, arg1, arg2 } => {
                    *self.reg_mut(dest) =
                        Gc::new(Value::Bool(self.atom_t(arg1)? <= self.atom_t(arg2)?));
                },
                IGt { dest, arg1, arg2 } => {
                    *self.reg_mut(dest) =
                        Gc::new(Value::Bool(self.atom_t(arg1)? > self.atom_t(arg2)?));
                },
                IGe { dest, arg1, arg2 } => {
                    *self.reg_mut(dest) =
                        Gc::new(Value::Bool(self.atom_t(arg1)? >= self.atom_t(arg2)?));
                },

                INeg { dest, src } => {
                    *self.reg_mut(dest) = Gc::new(Value::Int(-self.atom_t(src)?));
                },
                IAdd { dest, arg1, arg2 } => {
                    *self.reg_mut(dest) =
                        Gc::new(Value::Int(self.atom_t(arg1)? + self.atom_t(arg2)?));
                },
                ISub { dest, arg1, arg2 } => {
                    *self.reg_mut(dest) =
                        Gc::new(Value::Int(self.atom_t(arg1)? - self.atom_t(arg2)?));
                },
                IMul { dest, arg1, arg2 } => {
                    *self.reg_mut(dest) =
                        Gc::new(Value::Int(self.atom_t(arg1)? * self.atom_t(arg2)?));
                },
                IDiv { dest, arg1, arg2 } => {
                    *self.reg_mut(dest) =
                        Gc::new(Value::Int(self.atom_t(arg1)? / self.atom_t(arg2)?));
                },
                IRem { dest, arg1, arg2 } => {
                    *self.reg_mut(dest) =
                        Gc::new(Value::Int(self.atom_t(arg1)? % self.atom_t(arg2)?));
                },
                IMod { dest, arg1, arg2 } => {
                    let a = self.atom_t(arg1)?;
                    let b = self.atom_t(arg2)?;
                    *self.reg_mut(dest) = Gc::new(Value::Int((a % b + b) % b));
                },
                
                BoxNew { dest } => {
                    *self.reg_mut(dest) = Gc::new(Value::new_box());
                },
                BoxInit { lvbox, value} => {
                    *self.reg_t(lvbox)?.value.borrow_mut() = self.atom(value).clone();
                },
                BoxGet { dest, rvbox } => {
                    let value = self.atom_t(rvbox)?.value.borrow().clone();
                    *self.reg_mut(dest) = value;
                },
            
                TupleNew { dest, len } => {
                    *self.reg_mut(dest) = Gc::new(Value::new_tuple(self.atom_t(len)?));
                }
                TupleInit { lvtuple, index, value } => {
                    let tup = self.reg_t(lvtuple)?;
                    let index = self.atom_t(index)?;
                    let value = self.atom(value);
                    *tup.fields.borrow_mut().get_mut(index).ok_or(VMError::Bounds)? = value.clone();
                },
                TupleLen { dest, rvtuple } => {
                    let len = Gc::new(Value::Int(self.atom_t(rvtuple)?
                                                     .fields.borrow().len() as isize));
                    *self.reg_mut(dest) = len;
                }
                TupleGet { dest, rvtuple, index } => {
                    let value = {
                        let tup = self.atom_t(rvtuple)?;
                        let index = self.atom_t(index)?;
                        tup.fields.borrow().get(index).ok_or(VMError::Bounds)?.clone()
                    };
                    *self.reg_mut(dest) = value;
                }

                FnNew { dest, len } => {
                    *self.reg_mut(dest) = Gc::new(Value::new_fn(self.atom_t(len)?));
                },
                FnInitCode { lvfn, index } => {
                    *self.reg_t(lvfn)?.code.borrow_mut() =
                        Gc::new(Value::new_code_ptr(self.cob(index).clone(), 0));
                },
                FnInit { lvfn, index, value } => {
                    *self.reg_t(lvfn)?.env.borrow_mut()
                                      .get_mut(self.atom_t(index)?).ok_or(VMError::Bounds)? =
                        self.atom(value).clone();
                },
                FnCode { dest, rvfn } => {
                    let code = self.atom_t(rvfn)?.code.borrow().clone();
                    *self.reg_mut(dest) = code;
                },
                FnGet { dest, rvfn, index } => {
                    let v = {
                        let f = self.reg_t(rvfn)?;
                        let index = self.atom_t(index)?;
                        f.env.borrow().get(index).ok_or(VMError::Bounds)?.clone()
                    };
                    *self.reg_mut(dest) = v; 
                },

                ContNew { dest, len } => {
                    *self.reg_mut(dest) = Gc::new(Value::new_fn(self.atom_t(len)?));
                },
                ContInitCode { lvcont, offset } => {
                    *self.reg_t(lvcont)?.code.borrow_mut() =
                        Gc::new(Value::new_code_ptr(self.curr_proc.clone(),
                                                    self.offset_pc(offset)));
                },
                ContInit { lvcont, index, value } => {
                    *self.reg_t(lvcont)?.env.borrow_mut()
                                        .get_mut(self.atom_t(index)?).ok_or(VMError::Bounds)? =
                        self.atom(value).clone();
                },
                ContCode { dest, rvcont } => {
                    let code = self.atom_t(rvcont)?.code.borrow().clone();
                    *self.reg_mut(dest) = code;
                },
                ContGet { dest, rvcont, index } => {
                    let v = {
                        let f = self.reg_t(rvcont)?;
                        let index = self.atom_t(index)?;
                        f.env.borrow().get(index).ok_or(VMError::Bounds)?.clone()
                    };
                    *self.reg_mut(dest) = v; 
                },

                DenvNew { dest } => { *self.reg_mut(dest) = Gc::new(Value::new_denv()); }


                RecNew { dest, len } => {
                    *self.reg_mut(dest) = Gc::new(Value::new_record(self.atom_t(len)?));
                },
                RecInitType { lvrec, typ } => {
                    *self.reg_t(lvrec)?.typ.borrow_mut() = self.atom(typ).clone();
                },
                RecInit { lvrec, index, value } => {
                    *self.reg_t(lvrec)?.fields.borrow_mut().get_mut(self.atom_t(index)?)
                                                           .ok_or(VMError::Bounds)? =
                        self.atom(value).clone();
                },
                RecType { dest, rvrec } => {
                    let typ = self.atom_t(rvrec)?.typ.borrow().clone();
                    *self.reg_mut(dest) = typ;
                },
                RecGet { dest, rvrec, index } => {
                    let value = {
                        let rec = self.atom_t(rvrec)?;
                        let index = self.atom_t(index)?;
                        rec.fields.borrow().get(index).ok_or(VMError::Bounds)?.clone()
                    };
                    *self.reg_mut(dest) = value;
                },

                Brf { cond, offset } => {
                    if !self.atom_t(cond)? {
                        self.pc = self.offset_pc(offset);
                    }
                }

                IJmp { code } => {
                    let (new_proc, new_pc) = {
                        let code = self.reg_t(code)?;
                        (code.cob.clone(), code.pc)
                    };
                    self.curr_proc = new_proc;
                    self.pc = new_pc; 
                },

                Halt { value } => {
                    return Ok(self.atom(value).clone());
                },

                FLibOpen { dest, path } => {
                    let lib = {
                        Gc::new(Value::new_foreign_lib(self.atom_t(path)?)?)
                    };
                    *self.reg_mut(dest) = lib;
                },
                FLibSym { dest, lib, name } => {
                    let ptr = {
                        let lib = self.reg(lib);
                        let tlib: &Library = TryFrom::try_from(&**lib)?;
                        let ptr = unsafe {
                            tlib.get(self.atom_t(name)?.as_bytes())
                        }.map_err(VMError::ForeignLoad)?;
                        Gc::new(Value::new_ptr(lib.clone(), *ptr))
                    };
                    *self.reg_mut(dest) = ptr;
                },
                FFnNew { dest, ptr } => {
                    // FIXME: Need to copy lib pointer from ptr to f to prevent dangling:
                    let f = {
                        Gc::new(Value::new_ffn(self.reg_t(ptr)?.ptr))
                    };
                    *self.reg_mut(dest) = f;
                },
                FFnInitType { ffn, arg_types, ret_type } => {
                    let ffn = self.reg_t(ffn)?;
                    let arg_types = self.reg_t(arg_types)?;
                    let ret_type = self.atom(ret_type);
                    if ffn.cif.borrow().is_none() {
                        let arg_types_t: Vec<Type> = arg_types.fields.borrow().iter()
                                                              .map(as_ffi_type)
                                                              .collect::<Result<_, _>>()?;
                        *ffn.cif.borrow_mut() = Some(Cif::new(arg_types_t.into_iter(),
                                                              as_ffi_type(ret_type)?));
                    } else {
                        return Err(VMError::Reinitialization);
                    }
                },
                FFnInitCConv { ffn, conv_name } => { // TODO: Integrate into FFN_NEW
                    let ffn = self.reg_t(ffn)?;
                    match self.atom_t(conv_name)? {
                        "system" => { /* ffi_abi_FFI_DEFAULT_ABI, don't need to do anything */ },
                        "sysv64" => match *ffn.cif.borrow_mut() {
                            Some(ref mut cif) => cif.set_abi(FfiAbi::FFI_UNIX64),
                            None => return Err(VMError::Uninitialized)
                        },
                        _ => unimplemented!()
                    }
                },
                FFnCall { ffn } => {
                    let (kcode, res) = {
                        let k: &Closure = TryFrom::try_from(&*self.regs[1])?;
                        let args: &Tuple = TryFrom::try_from(&*self.regs[3])?;
                        let ffn = self.reg_t(ffn)?;
                        if let Some(ref cif) = *ffn.cif.borrow() {
                            let raw_cif = cif.as_raw_ptr();
                            let arg_types = unsafe {
                                slice::from_raw_parts((*raw_cif).arg_types, (*raw_cif).nargs as _)
                            };
                            let args: Vec<Arg> = arg_types.iter().zip(args.fields.borrow().iter())
                                                                 .map(|(&t, v)| as_arg(t, v))
                                                                 .collect::<Result<_, _>>()?;
                            let res_type = unsafe { *raw_cif }.rtype;
                            let res: u64 = match unsafe { (*res_type).size } {
                                1 => unimplemented!(),
                                2 => unimplemented!(),
                                4 => unimplemented!(),
                                8 => unsafe { cif.call(ffn.fn_ptr, args.as_slice()) },
                                _ => unimplemented!()
                            };
                            (k.code.borrow().clone(), Gc::new(inject(res_type, res)?))
                        } else {
                            return Err(VMError::Uninitialized);
                        }
                    };
                    // OPTIMIZE: tweak continuation calling convention to make
                    //           the 1->0 move unnecessary?:
                    self.regs[0] = self.regs[1].clone();
                    self.regs[1] = res;
                    let kcode_t: &CodePtr = TryFrom::try_from(&*kcode)?;
                    self.curr_proc = kcode_t.cob.clone();
                    self.pc = kcode_t.pc;
                }
            }
        }
    }
}
