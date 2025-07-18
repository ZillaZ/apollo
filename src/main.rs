use std::collections::HashSet;

use modules::parser::{Ast, BuildCache, NoirParser};
use pest::{iterators::Pairs, Parser};
use pest_derive::Parser;

use crate::modules::gcc::GccContext;
use crate::modules::memory::Memory;

mod modules;

#[derive(Debug)]
struct Args {
    pub debug: bool,
    pub path: String,
    pub out: String,
}

impl Default for Args {
    fn default() -> Self {
        Self {
            debug: false,
            path: "main.apo".into(),
            out: "out".into(),
        }
    }
}

#[derive(Parser)]
#[grammar = "spec.pest"]
pub struct Program;

fn main() {
    let args = parse_args();
    let parser = NoirParser::new();
    let mut memory = Memory::new("main".into());
    let context = gccjit::Context::default();
    let input = read_file(&args.path);
    let input = input.trim();
    let mut pairs: Pairs<Rule> = Program::parse(Rule::program, &input).unwrap();
    let mut ast = parser.gen_ast(&mut pairs, "main".into());
    read_core(parser, &mut ast);
    let mut cache = BuildCache::new();
    ast.build_imports(&mut cache);
    let gcc = GccContext::new(&context, ast.context.clone());
    let mut imports = HashSet::new();
    gcc.gen_bytecode(
        &mut ast,
        &mut imports,
        &mut memory,
        true,
        args.debug,
        true,
        args.out,
    );
}

fn read_file(path: &str) -> String {
    std::fs::read_to_string(path).unwrap()
}

fn get_args() -> Vec<String> {
    std::env::args().collect()
}

fn read_core(parser: NoirParser, ast: &mut Ast) {
    let path = std::env::var("APOLLO_CORE").unwrap();
    for file in std::fs::read_dir(path).unwrap() {
        let mut path = None;
        if let Ok(file) = file {
            if let Ok(file_type) = file.file_type() {
                if file_type.is_file()
                    && file
                        .file_name()
                        .to_string_lossy()
                        .to_string()
                        .ends_with(".apo")
                {
                    path = Some(file.path());
                }
            }
        }
        if let Some(path) = path {
            let data = std::fs::read_to_string(path).unwrap();
            let mut pairs = Program::parse(Rule::program, &data).unwrap();
            let core_ast = parser.gen_ast(&mut pairs, format!("core"));
            ast.extend(&core_ast);
        }
    }
}

fn parse_args() -> Args {
    let args_str = get_args();
    let mut args = Args::default();
    let mut next_is_path = false;
    let mut next_is_out = false;
    for arg in args_str.iter().skip(1) {
        if next_is_path {
            next_is_path = false;
            args.path = arg.into();
            continue;
        }
        if next_is_out {
            next_is_out = false;
            args.out = arg.into();
            continue;
        }
        match arg.as_str() {
            "--path" => next_is_path = true,
            "--out" => next_is_out = true,
            "--debug" => args.debug = true,
            _ => panic!(),
        }
    }
    args
}
