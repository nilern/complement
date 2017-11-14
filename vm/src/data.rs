use std::io;
use std::convert::TryFrom;
use std::collections::HashMap;
use std::cell::RefCell;
use std::mem;
use gc::{Gc, GcCell};
use libloading::Library;
use libffi::high;
use libffi::middle::{Cif, Type, Arg};
use libffi::low::ffi_type;

use code::Instr;
    
#[derive(Debug)]
pub enum VMError {
    OutOfInstrs,
    Uninitialized,
    Reinitialization,
    Type,
    Bounds,
    ForeignLoad(io::Error)
}
    
#[derive(Debug, Trace, Finalize)]
pub struct Program {
    pub register_demand: usize,
    pub procs: Vec<Gc<Proc>>,
    pub entry: usize
}

#[derive(Debug, Trace, Finalize)]
pub struct Proc {
    pub name: String,
    pub consts: Vec<ValueRef>,
    #[unsafe_ignore_trace]
    pub instrs: Vec<Instr>
}

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
pub struct ForeignPtr {
    #[unsafe_ignore_trace]
    pub ptr: *mut (),
    lib: ValueRef
}

#[derive(Debug)]
pub struct ForeignFn {
    pub fn_ptr: high::CodePtr,
    pub cif: RefCell<Option<Cif>>
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

    ForeignLib(#[unsafe_ignore_trace] Library),
    ForeignPtr(ForeignPtr),
    ForeignFn(#[unsafe_ignore_trace] ForeignFn),

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

    pub fn new_foreign_lib(path: &str) -> Result<Value, VMError> {
        match Library::new(path) {
            Ok(lib) => Ok(Value::ForeignLib(lib)),
            Err(err) => Err(VMError::ForeignLoad(err))
        }
    }

    pub fn new_ptr(lib: ValueRef, ptr: *mut ()) -> Value {
        Value::ForeignPtr(ForeignPtr { ptr: ptr, lib: lib })
    }
    
    pub fn new_ffn(ptr: *mut ()) -> Value {
        Value::ForeignFn(ForeignFn {
            fn_ptr: high::CodePtr(ptr as _),
            cif: RefCell::new(None)
        })
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

impl<'a> TryFrom<&'a Value> for &'a str {
    type Error = VMError;

    fn try_from(v: &Value) -> Result<&str, VMError> {
        if let &Value::String(ref s) = v { Ok(s) } else { Err(VMError::Type) }
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

impl<'a> TryFrom<&'a Value> for &'a Library {
    type Error = VMError;

    fn try_from(v: &Value) -> Result<&Library, VMError> {
        if let &Value::ForeignLib(ref lib) = v { Ok(lib) } else { Err(VMError::Type) }
    }
}

impl<'a> TryFrom<&'a Value> for &'a ForeignPtr {
    type Error = VMError;

    fn try_from(v: &Value) -> Result<&ForeignPtr, VMError> {
        if let &Value::ForeignPtr(ref ptr) = v { Ok(ptr) } else { Err(VMError::Type) }
    }
}

impl<'a> TryFrom<&'a Value> for &'a ForeignFn {
    type Error = VMError;

    fn try_from(v: &Value) -> Result<&ForeignFn, VMError> {
        if let &Value::ForeignFn(ref f) = v { Ok(f) } else { Err(VMError::Type) }
    }
}
    
impl<'a> TryFrom<&'a Value> for &'a Record {
    type Error = VMError;

    fn try_from(v: &Value) -> Result<&Record, VMError> {
        if let &Value::Record(ref r) = v { Ok(r) } else { Err(VMError::Type) }
    }
}

pub fn as_ffi_type(value: &ValueRef) -> Result<Type, VMError> {
    match &**value {
        &Value::Int(0) => Ok(Type::isize()),
        &Value::Int(2) => Ok(Type::u32()),
        _ => Err(VMError::Type)
    }
}

pub fn as_arg(typ: *mut ffi_type, value: &ValueRef) -> Result<Arg, VMError> {
    if typ == Type::isize().as_raw_ptr() {
        if let &Value::Int(ref i) = &**value {
            Ok(Arg::new(i))
        } else if let &Value::Char(ref c) = &**value {
            Ok(Arg::new(c))
        } else {
            unimplemented!()
        }
    } else {
        unimplemented!()
    }
}

#[cfg(target_pointer_width="64")]
pub fn inject(typ: *mut ffi_type, value: u64) -> Result<Value, VMError> {
    if typ == Type::isize().as_raw_ptr() {
        Ok(Value::Int(value as _))
    } else if typ == Type::u32().as_raw_ptr() {
        Ok(Value::Char(unsafe { mem::transmute(value as u32) }))
    } else {
        unimplemented!()
    }
}
