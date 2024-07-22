use modules::parser::NoirParser;
use pest::{iterators::Pairs, Parser};
use pest_derive::Parser;

use crate::modules::gcc::GccContext;
use crate::modules::memory::Memory;

mod modules;

#[derive(Parser)]
#[grammar = "spec.pest"]
pub struct Program;

fn main() {
    let parser = NoirParser::new();
    let mut memory = Memory::new("main".into());
    let context = gccjit::Context::default();
    let input = read_file("main.apo");
    let input = input.trim();
    let mut pairs: Pairs<Rule> = Program::parse(Rule::program, &input).unwrap();
    let ast = parser.gen_ast(&mut pairs, "main".into());
    println!("{:?}", ast.expressions);
    let gcc = GccContext::new(&context);
    gcc.gen_bytecode(&ast, &mut memory, true);
}

fn read_file(path: &str) -> String {
    std::fs::read_to_string(path).unwrap()
}
