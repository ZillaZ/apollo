use gccjit::{Block, Field, Function, LValue, Parameter, RValue, Struct, Type};
use super::structs::{Expr, Trait, Function as AstFunction, ImplMethod};
use std::collections::{HashMap, HashSet, VecDeque};

pub struct Memory<'a> {
    pub name: String,
    pub last_block: Option<(Block<'a>, Block<'a>)>,
    pub variables: HashMap<String, HashMap<String, LValue<'a>>>,
    pub functions: HashMap<String, Function<'a>>,
    pub builtins: Vec<String>,
    pub datatypes: HashMap<String, Type<'a>>,
    pub primitive_types: HashMap<Type<'a>, Type<'a>>,
    pub constructors: HashMap<String, HashMap<String, String>>,
    pub structs: HashMap<Struct<'a>, HashMap<String, i32>>,
    pub traits: HashMap<String, Trait>,
    pub function_scope: String,
    pub anon_count: u32,
    pub trait_types: HashMap<Type<'a>, String>,
    pub index: Option<LValue<'a>>,
    pub units: HashMap<Type<'a>, RValue<'a>>,
    pub continue_block: Option<Block<'a>>,
    pub blocks: HashMap<Block<'a>, bool>,
    pub field_types: HashMap<Field<'a>, Type<'a>>,
    pub impls: HashMap<Type<'a>, HashMap<String, HashMap<String, Function<'a>>>>,
    pub impl_methods: HashMap<String, HashMap<Type<'a>, Function<'a>>>,
    pub function_addresses: HashMap<String, RValue<'a>>,
    pub pointer_types: HashSet<Type<'a>>,
    pub imports: HashSet<String>,
    pub enum_variants: HashMap<Type<'a>, HashMap<String, (i32, Option<Field<'a>>)>>,
    pub block_tail_expr: VecDeque<Expr>,
    pub functions_with_traits: HashMap<String, AstFunction>,
    pub impl_with_traits: HashMap<String, (String, ImplMethod)>,
    pub variadic_args: HashMap<Function<'a>, Vec<Parameter<'a>>>,
    pub closures: HashMap<RValue<'a>, Function<'a>>,
    pub should_delay_ref_ops: bool
}

impl<'a> Memory<'a> {
    pub fn new(name: String) -> Self {
        let builtins = vec!["printf", "strnlen", "malloc", "memcpy", "realloc"]
            .iter()
            .map(|x| x.to_string())
            .collect::<_>();
        Self {
            name,
            builtins,
            last_block: None,
            variables: HashMap::new(),
            functions:HashMap::new(),
            datatypes:HashMap::new(),
            primitive_types: HashMap::new(),
            constructors: HashMap::new(),
            structs:HashMap::new(),
            traits:HashMap::new(),
            function_scope: "main".into(),
            anon_count: 0,
            trait_types:HashMap::new(),
            index: None,
            units:HashMap::new(),
            continue_block:None,
            impls:HashMap::new(),
            impl_methods:HashMap::new(),
            function_addresses:HashMap::new(),
            blocks:HashMap::new(),
            field_types:HashMap::new(),
            pointer_types:HashSet::new(),
            imports:HashSet::new(),
            enum_variants: HashMap::new(),
            block_tail_expr: VecDeque::new(),
            functions_with_traits: HashMap::new(),
            impl_with_traits: HashMap::new(),
            variadic_args: HashMap::new(),
            closures: HashMap::new(),
            should_delay_ref_ops: false
        }
    }
    pub fn unconst_type(&self, r#type: Type<'a>) -> Type<'a> {
        if let Some(unconst) = self.primitive_types.get(&r#type) {
            *unconst
        } else {
            r#type
        }
    }
}
