use modules::parser::NoirParser;
use pest::{iterators::Pairs, Parser};
use pest_derive::Parser;

use crate::modules::gcc::Memory;

mod modules;

#[derive(Parser)]
#[grammar = "spec.pest"]
struct Program;

fn main() {
    let parser = NoirParser::new();
    let memory = Memory::new();
    let input = read_file("main.noir");
    let input = input.trim();
    let mut pairs: Pairs<Rule> = Program::parse(Rule::program, &input).unwrap();
    let mut ast = parser.gen_ast(&mut pairs);
    println!("{:?}", ast);
    parser.gen_bytecode(memory, &mut ast);
}

fn read_file(path: &str) -> String {
    std::fs::read_to_string(path).unwrap()
}
