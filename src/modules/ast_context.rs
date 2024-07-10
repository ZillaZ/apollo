use std::collections::HashMap;
use super::structs::*;

#[derive(Clone, Debug)]
pub enum FinalValue {
    Char(char),
    String(String),
    Integet(i32),
    Float(f32),
    IntegerArray(Vec<i32>),
    FloatArray(Vec<f32>),
    StringArray(Vec<String>),
    BoolArray(Vec<bool>),
    CharArray(String),
}

#[derive(Clone, Debug)]
pub struct Scope {
    pub variables: HashMap<String, Value>,
    pub calls: HashMap<String, Vec<FinalValue>>,
}

#[derive(Debug)]
pub struct AstContext {
    pub functions: HashMap<String, Function>,
    pub imported: Vec<Import>,
    pub structs: HashMap<String, StructDecl>
}

impl AstContext {
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
            imported: Vec::new(),
            structs: HashMap::new()
        }
    }
}
