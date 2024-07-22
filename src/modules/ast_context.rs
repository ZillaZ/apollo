use super::structs::*;
use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct AstContext {
    pub functions: HashMap<String, Function>,
    pub imported: Vec<Import>,
    pub structs: HashMap<String, StructDecl>,
}

impl AstContext {
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
            imported: Vec::new(),
            structs: HashMap::new(),
        }
    }
}
