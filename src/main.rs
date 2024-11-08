use std::collections::HashSet;

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
    let args = get_args();
    let parser = NoirParser::new();
    let mut memory = Memory::new("main".into());
    let context = gccjit::Context::default();
    let input = read_file("main.apo");
    let input = input.trim();
    let mut pairs: Pairs<Rule> = Program::parse(Rule::program, &input).unwrap();
    let mut ast = parser.gen_ast(&mut pairs, "main".into());
    let gcc = GccContext::new(&context);
    let should_debug = if args.len() > 1 && args[2] == "--debug" {
        true
    } else {
        false
    };
    let mut imports = HashSet::new();
    gcc.gen_bytecode(&mut ast, &mut imports, &mut memory, true, should_debug);
    if args[1] == "run" {
        std::process::Command::new("./apollo").output().unwrap();
    }
}

fn read_file(path: &str) -> String {
    std::fs::read_to_string(path).unwrap()
}

fn get_args() -> Vec<String> {
    std::env::args().collect()
}
