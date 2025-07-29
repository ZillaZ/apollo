use super::{parser::BuildCache, structs::*};
use std::collections::HashMap;

macro_rules! extend_map {
    ($field:ident; $self:ident $context:ident) => {
        for (k, v) in $context.$field.iter() {
            $self.$field.insert(k.into(), v.clone());
        }
    };
    ($first:ident $($field:ident)+; $self:ident $context:ident) => {
        extend_map!($first; $self $context);
        extend_map!($($field)+; $self $context);
    };
}

#[derive(Clone, Debug, Default)]
pub struct AstContext {
    pub functions: HashMap<String, Function>,
    pub imported: Vec<Import>,
    pub structs: HashMap<String, StructDecl>,
    pub enums: HashMap<String, Enum>,
    pub impls: HashMap<String, Vec<Impl>>,
    pub variables: HashMap<String, HashMap<String, Value>>,
    pub traits: HashMap<String, Trait>,
    pub generic_types: HashMap<String, GenericType>,
    pub scope: String,
}

impl AstContext {
    pub fn extend(&mut self, context: &AstContext) {
        extend_map!(functions structs impls enums traits generic_types; self context);
    }

    pub fn extend_cache(&mut self, context: &BuildCache) {
        extend_map!(functions structs impls enums traits generic_types; self context);
    }
}
