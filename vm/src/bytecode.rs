#[derive(Debug, Clone, Copy)]
pub struct Instr(usize);

impl From<usize> for Instr {
    fn from(bits: usize) -> Instr {
        Instr(bits)     
    }
}
