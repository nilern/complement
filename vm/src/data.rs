use std::convert::TryFrom;
use std::collections::HashMap;
use gc::{Gc, GcCell};

use code::Instr;
    
#[derive(Debug)]
pub enum VMError {
    OutOfInstrs,
    Uninitialized,
    Type,
    Bounds
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
