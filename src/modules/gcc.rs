use std::ops::Add;

use gccjit::{Block, Context, Function, RValue, Type};
use pest::iterators::Pairs;

use crate::Rule;

pub struct GccContext<'a> {
    context: Context<'a>,
}

impl<'a> GccContext<'a> {
    pub fn new() -> Self {
        let context = Context::default();
        Self { context }
    }
    pub fn gen_bytecode(&self, pairs: &mut Pairs<Rule>) {
        let dt = self.context.new_int_type(4, true);
        let function =
            self.context
                .new_function(None, gccjit::FunctionType::Internal, dt, &[], "main", false);
        let block = function.new_block("main_block");

        for pair in pairs.next().unwrap().into_inner() {
            match pair.as_rule() {
                Rule::r#return => self.build_return(&mut pair.into_inner(), block),
                Rule::call => self.build_call(&mut pair.into_inner(), block),
                Rule::function => self.build_function(&mut pair.into_inner(), block),
                Rule::block => self.build_block(&mut pair.into_inner(), block),
                Rule::declaration => self.build_declaration(&mut pair.into_inner(), block),
                _ => unreachable!(),
            }
        }
    }
    pub fn build_return(&self, pairs: &mut Pairs<Rule>, block: Block<'_>) {}
    pub fn build_call(&self, pairs: &mut Pairs<Rule>, block: Block<'_>) {}
    pub fn build_function(&self, pairs: &mut Pairs<Rule>, block: Block<'_>) {}
    pub fn build_block(&self, pairs: &mut Pairs<Rule>, block: Block<'_>) {}
    pub fn build_declaration(&self, pairs: &mut Pairs<Rule>, block: Block<'_>) {}
}
