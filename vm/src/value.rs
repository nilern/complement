use gc::Gc;

use bytecode::Instr;

type ValueRef = Gc<Value>;

#[derive(Debug, Trace, Finalize)]
pub enum Value {
    Int(isize),
    Symbol(String)
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
