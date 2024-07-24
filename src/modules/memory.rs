use gccjit::{Function, LValue, Struct, Type};
use std::collections::HashMap;

use super::gcc::{GccContext, GccValues};

pub struct Memory<'a> {
    pub name: String,
    pub variables: HashMap<String, HashMap<String, LValue<'a>>>,
    pub functions: HashMap<String, Function<'a>>,
    pub builtins: Vec<String>,
    pub datatypes: HashMap<String, Type<'a>>,
    pub primitive_types: HashMap<Type<'a>, Type<'a>>,
    pub constructors: HashMap<String, HashMap<String, String>>,
    pub structs: HashMap<Struct<'a>, HashMap<String, i32>>,
    pub traits: HashMap<String, Vec<(String, Type<'a>)>>,
    pub function_scope: String,
    pub anon_count: u32,
    pub trait_types: HashMap<Type<'a>, String>,
    pub memory_tree: Vec<Box<Memory<'a>>>,
    pub extensions: HashMap<String, Box<dyn Fn(Vec<GccValues>)->GccValues>>
}

impl<'a> Memory<'a> {
    pub fn new(name: String) -> Self {
        let variables = HashMap::new();
        let functions = HashMap::new();
        let builtins = vec!["printf", "strnlen", "malloc", "memcpy"]
            .iter()
            .map(|x| x.to_string())
            .collect::<_>();
        let datatypes = HashMap::new();
        let primitive_types = HashMap::new();
        let constructors = HashMap::new();
        let structs = HashMap::new();
        let traits = HashMap::new();
        let function_scope = "main".into();
        let anon_count = 0;
        let trait_types = HashMap::new();
        let memory_tree = Vec::new();
        let extensions = HashMap::new();
        Self {
            name,
            variables,
            functions,
            builtins,
            datatypes,
            primitive_types,
            constructors,
            structs,
            traits,
            function_scope,
            anon_count,
            trait_types,
            memory_tree,
            extensions,
        }
    }
    pub fn unconst_type(&self, r#type: Type<'a>) -> Type<'a> {
        if let Some(unconst) = self.primitive_types.get(&r#type) {
            unconst.clone()
        } else {
            r#type
        }
    }
}
