use modules::parser::NoirParser;
use pest::{iterators::Pairs, Parser};
use pest_derive::Parser;

use crate::modules::gcc::{GccContext, Memory};

mod modules;

#[derive(Parser)]
#[grammar = "spec.pest"]
pub struct Program;

fn main() {
    let parser = NoirParser::new();
    let memory = Memory::new();
    let input = read_file("main.apo");
    let input = input.trim();
    let mut pairs: Pairs<Rule> = Program::parse(Rule::program, &input).unwrap();
    let mut ast = parser.gen_ast(&mut pairs);
    println!("{:?}", ast.expressions);
    let gcc = GccContext::new(ast.context);
    gcc.gen_bytecode(memory, &mut ast.expressions, &ast.imports);
}

fn read_file(path: &str) -> String {
    std::fs::read_to_string(path).unwrap()
}
