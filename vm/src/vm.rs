use std::convert::TryFrom;
use std::slice;
use gc::Gc;
use libloading::Library;
use libffi::middle::{Cif, Type, Arg, FfiAbi};

use code::*;
use data::{VMError, Program, VMBox, Tuple, Record, Proc, ForeignFn, Closure, CodePtr, ForeignPtr,
           Value, ValueRef, as_ffi_type, as_arg, inject};

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

                FLIB_OPEN => {
                    let (di, lib) = {
                        let (di, ni): (DestReg, Atom<&str>) = instr.parse();
                        let name = self.atom_t(ni)?;
                        (di, Gc::new(Value::new_foreign_lib(name)?))   
                    };
                    *self.reg_mut(di) = lib;
                },
                FLIB_SYM => {
                    let (di, ptr) = {
                        let (di, li, ni): (DestReg, AnySrcReg, Atom<&str>) = instr.parse();
                        let lib = self.reg(li);
                        let tlib: &Library = TryFrom::try_from(&**lib)?;
                        let name = self.atom_t(ni)?;
                        let ptr = unsafe { tlib.get(name.as_bytes()) }.map_err(VMError::ForeignLoad)?;
                        (di, Gc::new(Value::new_ptr(lib.clone(), *ptr)))
                    };
                    *self.reg_mut(di) = ptr;
                },
                FFN_NEW => { // FIXME: Need to copy lib pointer from ptr to f to prevent dangling:
                    let (di, f) = {
                        let (di, pi): (DestReg, SrcReg<&ForeignPtr>) = instr.parse();
                        let ptr = self.reg_t(pi)?;
                        (di, Gc::new(Value::new_ffn(ptr.ptr)))
                    };
                    *self.reg_mut(di) = f;
                },
                FFN_INIT_TYPE => {
                    let (fi, ai, ri): (SrcReg<&ForeignFn>, SrcReg<&Tuple>, AnyAtom) = instr.parse();
                    let f = self.reg_t(fi)?;
                    let arg_types = self.reg_t(ai)?;
                    let ret_type = self.atom(ri);
                    if f.cif.borrow().is_none() {
                        let arg_types_t: Vec<Type> = arg_types.fields.borrow().iter()
                                                              .map(as_ffi_type)
                                                              .collect::<Result<_, _>>()?;
                        *f.cif.borrow_mut() = Some(Cif::new(arg_types_t.into_iter(),
                                                            as_ffi_type(ret_type)?));
                    } else {
                        return Err(VMError::Reinitialization);
                    }
                },
                FFN_INIT_CCONV => { // TODO: Integrate into FFN_NEW
                    let (fi, cci): (SrcReg<&ForeignFn>, Atom<&str>) = instr.parse();
                    let f = self.reg_t(fi)?;
                    let cconv = self.atom_t(cci)?;
                    match cconv {
                        "system" => { /* ffi_abi_FFI_DEFAULT_ABI, don't need to do anything */ },
                        "sysv64" => match *f.cif.borrow_mut() {
                            Some(ref mut cif) => cif.set_abi(FfiAbi::FFI_UNIX64),
                            None => return Err(VMError::Uninitialized)
                        },
                        _ => unimplemented!()
                    }
                },
                FFN_CALL => {
                    let (kcode, res) = {
                        let fi: SrcReg<&ForeignFn> = instr.parse();
                        let k: &Closure = TryFrom::try_from(&*self.regs[1])?;
                        let args: &Tuple = TryFrom::try_from(&*self.regs[3])?;
                        let f = self.reg_t(fi)?;
                        if let Some(ref cif) = *f.cif.borrow() {
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
                                8 => unsafe { cif.call(f.fn_ptr, args.as_slice()) },
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
                },
                
                op => panic!("unimplemented op {:?}", op)
            }
        }
    }
}
