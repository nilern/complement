use std::collections::HashMap;

use gc::{Gc, GcCell};

use bytecode::Instr;

pub type ValueRef = Gc<Value>;

#[derive(Debug, Trace, Finalize)]
pub enum Value {
    Int(isize),
    Bool(bool),
    
    Symbol(String),

    Tuple(GcCell<Vec<ValueRef>>),

    Null,
    Box(GcCell<ValueRef>),
    
    CodePtr(Gc<Proc>, usize),
    Fn(GcCell<Option<Gc<Proc>>>, GcCell<Vec<ValueRef>>),
    Cont(GcCell<Gc<Value>>, GcCell<Vec<ValueRef>>),
    
    Denv(HashMap<String, ValueRef>)
}

impl Value {
    pub fn new_tuple(len: usize) -> Value {
        Value::Tuple(GcCell::new(vec![Gc::new(Value::Null); len]))     
    }

    pub fn new_box() -> Value {
        Value::Box(GcCell::new(Gc::new(Value::Null)))
    }

    pub fn new_fn(len: usize) -> Value {
        Value::Fn(GcCell::new(None),
                  GcCell::new(vec![Gc::new(Value::Null); len]))
    }
    
    pub fn new_cont(len: usize) -> Value {
        Value::Cont(GcCell::new(Gc::new(Value::Null)),
                    GcCell::new(vec![Gc::new(Value::Null); len]))
    }

    pub fn new_denv() -> Value {
        Value::Denv(HashMap::new())     
    }
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
