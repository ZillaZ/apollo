use gccjit::{Block, Function, LValue, RValue, Struct, Type};
use std::collections::{HashMap, HashSet};

use super::gcc::{GccContext, GccValues};

pub struct Memory<'a> {
    pub name: String,
    pub last_block: Option<Block<'a>>,
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
    pub index: Option<LValue<'a>>,
    pub units: HashMap<Type<'a>, RValue<'a>>,
    pub continue_block: Option<Block<'a>>,
    pub blocks: HashMap<Block<'a>, bool>,
    pub implementations: HashMap<String, Function<'a>>,
    pub impls: HashMap<Type<'a>, Vec<(String, Function<'a>)>>,
    pub memory_tree: Vec<Box<Memory<'a>>>,
    pub extensions: HashMap<String, Box<dyn Fn(Vec<GccValues>) -> GccValues>>,
}

impl<'a> Memory<'a> {
    pub fn new(name: String) -> Self {
        let last_block = None;
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
        let index = None;
        let units = HashMap::new();
        let continue_block = None;
        let blocks = HashMap::new();
        let implementations = HashMap::new();
        let impls = HashMap::new();
        let memory_tree = Vec::new();
        let extensions = HashMap::new();
        Self {
            name,
            last_block,
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
            index,
            units,
            continue_block,
            implementations,
            impls,
            blocks,
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
