use super::structs::*;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug)]
pub struct AstContext {
    pub functions: HashMap<String, Function>,
    pub imported: Vec<Import>,
    pub structs: HashMap<String, StructDecl>,
    pub variables: HashMap<String, HashMap<String, Value>>,
    pub scope: String,
}

impl AstContext {
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
            imported: Vec::new(),
            structs: HashMap::new(),
            variables: HashMap::new(),
            scope: String::new(),
        }
    }
}
