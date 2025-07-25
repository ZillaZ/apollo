use super::{parser::BuildCache, structs::*};
use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct AstContext {
    pub functions: HashMap<String, Function>,
    pub imported: Vec<Import>,
    pub structs: HashMap<String, StructDecl>,
    pub enums: HashMap<String, Enum>,
    pub impls: HashMap<String, Vec<Impl>>,
    pub variables: HashMap<String, HashMap<String, Value>>,
    pub scope: String,
}

impl AstContext {
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
            imported: Vec::new(),
            structs: HashMap::new(),
            enums: HashMap::new(),
            impls: HashMap::new(),
            variables: HashMap::new(),
            scope: String::new(),
        }
    }

    pub fn extend(&mut self, context: &AstContext) {
        for (k, v) in context.functions.iter() {
            self.functions.insert(k.into(), v.clone());
        }
        for (k, v) in context.structs.iter() {
            self.structs.insert(k.into(), v.clone());
        }
        for (k, v) in context.impls.iter() {
            self.impls.insert(k.into(), v.clone());
        }
        for (k, v) in context.enums.iter() {
            self.enums.insert(k.into(), v.clone());
        }
    }

    pub fn extend_cache(&mut self, context: &BuildCache) {
        for (k, v) in context.functions.iter() {
            self.functions.insert(k.into(), v.clone());
        }
        for (k, v) in context.structs.iter() {
            self.structs.insert(k.into(), v.clone());
        }
        for (k, v) in context.impls.iter() {
            self.impls.insert(k.into(), v.clone());
        }
        for (k, v) in context.enums.iter() {
            self.enums.insert(k.into(), v.clone());
        }
    }
}
