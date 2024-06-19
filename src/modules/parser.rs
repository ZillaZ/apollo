use pest::{
    iterators::{Pair, Pairs},
    pratt_parser::{Assoc, Op, PrattParser},
};

use crate::{modules::structs::*, Rule};

use super::{
    gcc::GccContext,
    structs::{MathOp, Operations, UnaryOp},
};

pub struct NoirParser<'a> {
    pub pratt_parser: PrattParser<Rule>,
    context: GccContext<'a>,
}

impl<'a> NoirParser<'a> {
    pub fn new() -> Self {
        let pratt_parser = PrattParser::new()
            .op(Op::infix(Rule::add, Assoc::Left) | Op::infix(Rule::sub, Assoc::Left))
            .op(Op::infix(Rule::mul, Assoc::Left) | Op::infix(Rule::div, Assoc::Left))
            .op(Op::prefix(Rule::unary_minus));
        let context = GccContext::new();
        Self {
            pratt_parser,
            context,
        }
    }

    pub fn gen_bytecode(&self, pairs: &mut Pairs<Rule>) {
        self.context.gen_bytecode(pairs);
    }

    pub fn gen_ast(&self, pairs: &mut Pairs<Rule>) -> Vec<Expr> {
        self.build_expression(&mut pairs.next().unwrap().into_inner())
    }

    fn build_expression(&self, pairs: &mut Pairs<Rule>) -> Vec<Expr> {
        let mut expressions = Vec::new();
        for pair in pairs {
            let expr = match pair.as_rule() {
                Rule::r#return => Expr::Return(self.build_return(&mut pair.into_inner())),
                Rule::call => Expr::Call(self.build_call(&mut pair.into_inner())),
                Rule::function => Expr::Function(self.build_function(&mut pair.into_inner())),
                Rule::block => Expr::Block(self.build_block(&mut pair.into_inner())),
                Rule::declaration => Expr::Declaration(self.build_declaration(&mut pair.into_inner())),
                _ => unreachable!(),
            };
            expressions.push(expr);
        }
        expressions
    }

    fn build_math(&self, pairs: &mut Pairs<Rule>) -> MathOp {
        self.pratt_parser
            .map_primary(|primary| match primary.as_rule() {
                Rule::atom => MathOp::Atom(self.build_atom(&mut primary.into_inner())),
                Rule::math => self.build_math(&mut primary.into_inner()),
                rule => unreachable!("Rule {:?}", rule),
            })
            .map_infix(|lhs, infix, rhs| {
                let op = match infix.as_rule() {
                    Rule::add => Operations::Add,
                    Rule::sub => Operations::Sub,
                    Rule::mul => Operations::Mul,
                    Rule::div => Operations::Div,
                    _ => unreachable!("Infix wtf"),
                };
                MathOp::BinaryOp(BinaryOp {
                    lhs: Box::new(lhs),
                    op,
                    rhs: Box::new(rhs),
                })
            })
            .map_prefix(|prefix, value| {
                let prefix = match prefix.as_rule() {
                    Rule::unary_minus => Operations::Neg,
                    rule => unreachable!("Prefix {:?}", rule),
                };
                MathOp::UnaryOp(UnaryOp {
                    prefix,
                    value: Box::new(value),
                })
            })
            .parse(pairs)
    }

    pub fn build_return(&self, pairs: &mut Pairs<Rule>) -> Return {
        let pair = pairs.next().unwrap();
        let value = self.build_value(&mut pair.into_inner());
        Return { value }
    }

    fn build_value(&self, pairs: &mut Pairs<Rule>) -> Value {
        let eval = pairs.peek().unwrap();
        match eval.as_rule() {
            Rule::math => Value::Math(Box::new(self.build_math(&mut eval.into_inner()))),
            Rule::call => Value::Call(self.build_call(&mut eval.into_inner())),
            Rule::block => Value::Block(Box::new(self.build_block(&mut eval.into_inner()))),
            Rule::name => Value::Name(self.build_name(eval)),
            Rule::atom => Value::Atom(Box::new(self.build_atom(&mut eval.into_inner()))),
            Rule::string_value => self.build_string_value(eval),
            Rule::integer => self.build_integer(eval),
            Rule::float => self.build_float(eval),
            _ => unreachable!(),
        }
    }

    fn build_call(&self, pairs: &mut Pairs<Rule>) -> Call {
        let pair = pairs.next().unwrap();
        let pairs = pair.into_inner();
        let mut call = Call {
            name: String::new(),
            args: Vec::new()
        };
        for eval in pairs {
            match eval.as_rule() {
                Rule::name => call.name = self.build_name(eval),
                Rule::param => call.args = self.build_param(&mut eval.into_inner()),
                _ => unreachable!()
            }
        }
        call
    }

    fn build_function(&self, pairs: &mut Pairs<Rule>) -> Function {
        let mut function = Function {
            name: String::new(),
            args: Vec::new(),
            return_type: None,
            block: Box::new(Block {
                expr: Vec::new(),
                box_return: None
            })
        };
        for pair in pairs.clone() {
            match pair.as_rule() {
                Rule::name => function.name = self.build_name(pair),
                Rule::args => function.args = self.build_args(&mut pair.into_inner()),
                Rule::return_type => function.return_type = Some(self.build_datatype(pairs)),
                Rule::block => function.block = Box::new(self.build_block(&mut pair.into_inner())),
                _ => unreachable!()
            }
        }
        function
    }

    fn build_atom(&self, pairs: &mut Pairs<Rule>) -> Atom {
        let mut atom = Atom {
            is_neg: false,
            value: Value::Int(0)
        };
        for pair in pairs {
            match pair.as_rule() {
                Rule::unary_minus => atom.is_neg = true,
                Rule::primary => atom.value = self.build_value(&mut pair.into_inner()),
                _ => unreachable!()
            };
        }
        atom
    }

    fn build_block(&self, pairs: &mut Pairs<Rule>) -> Block {
        let mut block = Block {
            expr: Vec::new(),
            box_return: None
        };
        for pair in pairs {
            let expressions = self.build_expression(&mut pair.into_inner());
            for expression in expressions {
                match expression {
                    Expr::Return(r#return) => block.box_return = Some(r#return),
                    val => block.expr.push(Box::new(val))
                }
            }
        }
        block
    }

    fn build_declaration(&self, pairs: &mut Pairs<Rule>) -> Declaration {
        let mut declaration = Declaration {
            name: String::new(),
            datatype: None,
            value: Value::Int(0)
        };
        for pair in pairs {
            match pair.as_rule() {
                Rule::name => declaration.name = self.build_name(pair),
                Rule::value => declaration.value = self.build_value(&mut pair.into_inner()),
                Rule::datatype => declaration.datatype = Some(self.build_datatype(&mut pair.into_inner())),
                _ => unreachable!()
            }
        }
        declaration
    }

    fn build_string_value(&self, pair: Pair<Rule>) -> Value {
        Value::String(pair.as_str().into())
    }

    fn build_integer(&self, pair: Pair<Rule>) -> Value {
        Value::Int(pair.as_str().parse().unwrap())
    }

    fn build_float(&self, pair: Pair<Rule>) -> Value {
        Value::Float(pair.as_str().parse().unwrap())
    }

    fn build_name(&self, pair: Pair<Rule>) -> String {
        pair.as_str().into()
    }

    fn build_param(&self, pairs: &mut Pairs<Rule>) -> Vec<Parameter> {
        let mut parameters = Vec::new();
        for pair in pairs {
            let parameter = match pair.as_rule() {
                Rule::name => Parameter::Name(self.build_name(pair)),
                Rule::value => Parameter::Value(self.build_value(&mut pair.into_inner())),
                _ => unreachable!()
            };
            parameters.push(parameter);
        }
        parameters
    }

    fn build_args(&self, pairs: &mut Pairs<Rule>) -> Vec<Arg> {
        let mut args = Vec::new();
        for pair in pairs {
            let mut arg = Arg {
                name: String::new(),
                datatype: DataType::Int(4)
            };
            match pair.as_rule() {
                Rule::v => args.push(arg),
                Rule::name => arg.name = self.build_name(pair),
                Rule::datatype => arg.datatype = self.build_datatype(&mut pair.into_inner()),
                _ => unreachable!()
            }
        };
        args
    }

    fn build_datatype(&self, pairs: &mut Pairs<Rule>) -> DataType {
        let eval = pairs.peek().unwrap();
        match eval.as_rule() {
            Rule::float_type => self.build_float_type(&mut eval.into_inner()),
            Rule::int_type => self.build_int_type(&mut eval.into_inner()),
            Rule::string_type => DataType::String,
            _ => unreachable!()
        }
    }

    fn build_int_type(&self, pairs: &mut Pairs<Rule>) -> DataType {
        let mut bytecount = 4;
        let mut is_unsigned = false;
        for pair in pairs {
            match pair.as_rule() {
                Rule::integer => bytecount = pair.as_str().parse().unwrap(),
                Rule::unsigned => is_unsigned = true,
                _ => unreachable!()
            }
        }
        if is_unsigned {
            return DataType::UInt(bytecount)
        }
        DataType::Int(bytecount)
    }

    fn build_float_type(&self, pairs: &mut Pairs<Rule>) -> DataType {
        let mut bytecount = 4;
        let mut is_unsigned = false;
        for pair in pairs {
            match pair.as_rule() {
                Rule::integer => bytecount = pair.as_str().parse().unwrap(),
                Rule::unsigned => is_unsigned = true,
                _ => unreachable!()
            }
        }
        if is_unsigned {
            return DataType::UFloat(bytecount)
        }
        DataType::Float(bytecount)
    }
}
