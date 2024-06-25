use std::{collections::HashMap, ops::{Add, BitAnd, BitOr, Div, Mul, Sub}};
use gccjit::{BinaryOp, Block, ComparisonOp, Context, Function, LValue, Parameter, RValue, ToRValue, Type, UnaryOp};

use crate::modules::structs::Otherwise;

use super::structs::{self, DataType, Value};
use super::structs::Expr;

pub enum Helper {
    Binary(BinaryOp),
    Comp(ComparisonOp)
}

pub struct Memory<'a> {
    pub variables: HashMap<String, LValue<'a>>,
    pub functions: HashMap<String, Function<'a>>,
    pub function_args: HashMap<String, HashMap<String, Parameter<'a>>>,
    pub builtins: Vec<String>,
    pub function_scope: String,
    pub anon_count: u32
}

impl <'a>Memory<'a> {
    pub fn new() -> Self {
        let variables = HashMap::new();
        let functions = HashMap::new();
        let function_args = HashMap::new();
        let builtins = vec!["printf", "strnlen", "malloc"].iter().map(|x| x.to_string()).collect::<_>();
        let function_scope = "main".into();
        let anon_count = 0;
        Self { variables, functions, function_args, builtins, function_scope, anon_count }
    }
}

pub struct GccContext<'a> {
    context: Context<'a>,
}

impl<'a> GccContext<'a> {
    pub fn new() -> Self {
        let context = Context::default();
        context.set_optimization_level(gccjit::OptimizationLevel::Aggressive);
        Self { context }
    }

    fn calc_len(&'a self, memory: &mut Memory<'a>) {
        let int_type = self.context.new_c_type(gccjit::CType::Int);
        let param = self.context.new_parameter(None, int_type, "number");
        let function = self.context.new_function(None, gccjit::FunctionType::Internal, self.context.new_c_type(gccjit::CType::SizeT), &[param], "number_len", false);
        let block = function.new_block("number_len");
        let var = function.new_local(None, int_type, "mul");
        let count = function.new_local(None, int_type, "count");
        block.add_assignment(None, count, self.context.new_rvalue_from_int(int_type, 1));
        block.add_assignment(None, var, self.context.new_rvalue_from_int(int_type, 10));
        let param = function.get_param(0).to_rvalue();
        let condition = self.context.new_comparison(None, ComparisonOp::GreaterThan, var.to_rvalue(), param);
        let comp_block = function.new_block("comp_block");
        let then_block = function.new_block("then_block");
        let else_block = function.new_block("else_block");
        block.end_with_jump(None, comp_block);
        comp_block.end_with_conditional(None, condition, then_block, else_block);
        then_block.end_with_return(None, self.context.new_cast(None, count.to_rvalue(), self.context.new_c_type(gccjit::CType::SizeT)));
        else_block.add_assignment_op(None, count, BinaryOp::Plus, self.context.new_rvalue_from_int(int_type, 1));
        else_block.add_assignment_op(None, var, BinaryOp::Mult, self.context.new_rvalue_from_int(int_type, 10));
        else_block.end_with_jump(None, comp_block);
        memory.functions.insert("std_number_len".into(), function);
    }

    fn str_conv(&'a self, memory: &mut Memory<'a>) {
        let string_type = self.context.new_string_literal("kk").get_type();
        let int_type = self.context.new_c_type(gccjit::CType::Int);
        let char_type = self.context.new_c_type(gccjit::CType::Char);
        let char_ptr_type = char_type.make_pointer();
        let param = self.context.new_parameter(None, int_type, "number");
        let function = self.context.new_function(None, gccjit::FunctionType::Internal, char_ptr_type, &[param], "string", false);
        memory.functions.insert("string".into(), function);
        let block = function.new_block("str_conv");
        let len = function.new_local(None, self.context.new_c_type(gccjit::CType::SizeT), "number_len");
        let number_lvalue = function.get_param(0);
        let number = number_lvalue.to_rvalue();
        let call = self.context.new_call(None, *memory.functions.get("std_number_len").unwrap(), &[number]);
        block.add_assignment(None, len, call);
        let rev_allocation = self.context.new_call(None, *memory.functions.get("malloc").unwrap(), &[call]);
        let rev_allocation = self.context.new_cast(None, rev_allocation, char_ptr_type);
        let rev_buffer = function.new_local(None, rev_allocation.get_type(), "rev_buffer");
        block.add_assignment(None, rev_buffer, rev_allocation);
        let allocation = self.context.new_call(None, *memory.functions.get("malloc").unwrap(), &[call]);
        let allocation = self.context.new_cast(None, allocation, char_ptr_type);
        let buffer = function.new_local(None, allocation.get_type(), "buffer");
        block.add_assignment(None, buffer, allocation);
        let index = function.new_local(None, int_type, "index");
        block.add_assignment(None, index, self.context.new_rvalue_from_int(int_type, 0));
        let rev_build = function.new_block("rev_build");
        block.end_with_jump(None, rev_build);
        let condition = self.context.new_comparison(None, ComparisonOp::GreaterThan, number, self.context.new_rvalue_from_int(int_type, 9));
        let continue_block = function.new_block("continue_block");
        let remainder = function.new_local(None, int_type, "remainder");
        let ascii_char = self.context.new_binary_op(None, BinaryOp::Modulo, int_type, number, self.context.new_rvalue_from_int(int_type, 10));
        let ascii_char = self.context.new_binary_op(None, BinaryOp::Plus, int_type, ascii_char, self.context.new_rvalue_from_int(int_type, 48));
        rev_build.add_assignment(None, remainder, ascii_char);
        rev_build.add_assignment_op(None, number_lvalue, BinaryOp::Divide, self.context.new_rvalue_from_int(int_type, 10));
        let char_access = self.context.new_array_access(None, rev_buffer, index.to_rvalue());
        rev_build.add_assignment(None, char_access, self.context.new_cast(None, remainder, char_type));
        rev_build.add_assignment_op(None, index, BinaryOp::Plus, self.context.new_rvalue_from_int(int_type, 1));
        let rev_buf_end = self.context.new_array_access(None, rev_buffer, index.to_rvalue());
        let last = self.context.new_binary_op(None, BinaryOp::Plus, int_type, number, self.context.new_rvalue_from_int(int_type, 48));
        continue_block.add_assignment(None, rev_buf_end, self.context.new_cast(None, last, char_type));
        let build = function.new_block("build");
        continue_block.end_with_jump(None, build);
        let cond = self.context.new_comparison(None, ComparisonOp::GreaterThan, index.to_rvalue(), self.context.new_rvalue_from_int(int_type, -1));
        let end_block = function.new_block("end_block");
        let access_index = self.context.new_binary_op(None, BinaryOp::Minus, int_type, self.context.new_cast(None, len.to_rvalue(), int_type), index.to_rvalue());
        let access_index = self.context.new_binary_op(None, BinaryOp::Minus, int_type, access_index, self.context.new_rvalue_from_int(int_type, 1));
        let access = self.context.new_array_access(None, buffer, access_index);
        let rev_access = self.context.new_array_access(None, rev_buffer, index.to_rvalue());
        build.add_assignment(None, access, rev_access.to_rvalue());
        build.add_assignment_op(None, index, BinaryOp::Minus, self.context.new_rvalue_from_int(int_type, 1));
        build.end_with_conditional(None, cond, build, end_block);
        rev_build.end_with_conditional(None, condition, rev_build, continue_block);
        let log = self.context.new_call(None, *memory.functions.get("printf").unwrap(), &[self.context.new_cast(None, buffer.to_rvalue(), self.context.new_c_type(gccjit::CType::ConstCharPtr))]);
        let log_var = function.new_local(None, int_type, "logkk");
        end_block.add_assignment(None, log_var, log);
        end_block.end_with_return(None, buffer.to_rvalue());
    }

    pub fn gen_bytecode(&'a self, mut memory: Memory<'a>, ast: &mut Vec<Expr>) {
        self.add_builtin_functions(&mut memory);
        self.add_standard_functions(&mut memory);
        let dt = self.context.new_int_type(4, true);
        let function =
            self.context
                .new_function(None, gccjit::FunctionType::Exported, dt, &[], "main", false);
        let mut block = function.new_block("initial");

        for expr in ast {
            let reference = &mut memory;
            match expr {
                Expr::Return(ref rtn) =>  { self.build_return(rtn, block, reference); },
                Expr::Call(ref call) => {
                    let function = block.get_function();
                    let result = self.parse_call(call, block, reference).unwrap();
                    let anon = function.new_local(None, result.get_type(), &format!("_{}", memory.anon_count));
                    memory.anon_count += 1;
                    block.add_assignment(None, anon, result);
                },
                Expr::Function(ref function) => { self.parse_function(function, block, reference); },
                Expr::Block(ref ast_block) => { self.parse_block(ast_block, block, reference); },
                Expr::Declaration(ref declaration) => { self.parse_declaration(declaration, block, reference); },
                Expr::If(ref ast_if) => { block = self.parse_if(ast_if, block, reference); }
            }
        }
        self.context.dump_to_file("noir.c", false);
        self.context.compile_to_file(gccjit::OutputKind::Executable, "noir");
        self.context.compile_to_file(gccjit::OutputKind::Assembler, "noir.s");
    }

    fn add_builtin_functions(&'a self, memory: &mut Memory<'a>) {
        for i in 0..memory.builtins.len() {
            let name = &memory.builtins[i];
            let function = self.context.get_builtin_function(name);
            memory.functions.insert(name.clone(), function);
        }
    }

    fn add_standard_functions(&'a self, memory: &mut Memory<'a>) {
        self.calc_len(memory);
        self.str_conv(memory);
    }

    fn build_return(&'a self, rtn: &structs::Return, block: Block<'a>, memory: &mut Memory<'a>) {
        let rvalue = self.parse_value(&rtn.value, block, memory);
        match rvalue {
            Some(mut value) => {
                let function_return_type = block.get_function().get_return_type();
                if !function_return_type.is_compatible_with(value.get_type()) {
                    value = self.context.new_cast(None, value, function_return_type);
                }
                block.end_with_return(None, value);
            }
            None => block.end_with_void_return(None)
        }
    }

    fn parse_value(&'a self, value: &structs::Value, block: Block<'a>, memory: &mut Memory<'a>) -> Option<RValue<'a>> {
        match value {
            Value::Int(number) => self.parse_int(*number),
            Value::Float(number) => self.parse_float(*number),
            Value::String(ref string) => self.parse_string(string),
            Value::Name(ref name) => self.parse_name(name, memory, block),
            Value::Bool(boolean) => self.parse_bool(*boolean),
            Value::Atom(ref atom) => self.parse_atom(atom, block, memory),
            Value::Operation(operation) => self.parse_operation(operation, block, memory),
            Value::Call(call) => self.parse_call(call, block, memory),
            Value::Block(ref ast_block) => {
                let args : Vec<(String, RValue<'a>)> = memory.variables.iter().map(|x| (x.0.clone(), x.1.to_rvalue())).collect();
                let params : Vec<Parameter<'a>> = args.iter().map(|x| self.context.new_parameter(None, x.1.get_type(), x.0.clone())).collect();
                let return_value = self.parse_value(&ast_block.box_return.as_ref().unwrap().value, block, memory).unwrap();
                let name = format!("anon_{}", memory.anon_count);
                memory.anon_count += 1;
                let function = self.context.new_function(None, gccjit::FunctionType::Internal, return_value.get_type(), params.as_slice(), &name, false);
                let new_block = function.new_block("anon_block");
                memory.functions.insert(name.clone(), function);
                self.parse_block(ast_block, new_block, memory);
                Some(self.context.new_call(None, function, args.iter().map(|x| x.1).collect::<Vec<_>>().as_slice()))
            }
            _ => todo!()
        }
    }

    fn parse_block(&'a self, ast_block: &structs::Block, mut new_block: Block<'a>, memory: &mut Memory<'a>) -> Option<RValue<'a>> {
        for expr in ast_block.expr.iter() {
            match **expr {
                Expr::Block(ref ast_block) => { self.parse_block(&Box::new(ast_block), new_block, memory); },
                Expr::Call(ref call) => {
                    let function = new_block.get_function();
                    let result = self.parse_call(call, new_block, memory).unwrap();
                    let anon = function.new_local(None, result.get_type(), &format!("_{}", memory.anon_count));
                    memory.anon_count += 1;
                    new_block.add_assignment(None, anon, result);
                },
                Expr::Declaration(ref declaration) => { self.parse_declaration(declaration, new_block, memory); },
                Expr::Function(ref function) =>  { self.parse_function(function, new_block, memory); },
                Expr::If(ref ast_if) => { new_block = self.parse_if(ast_if, new_block, memory); },
                _ => todo!()
                //Expr::Return(ref ast_return) => { self.build_return(ast_return, new_block, memory); }
            };
        }
        match &ast_block.box_return {
            Some(ref rtn) => {
                self.build_return(rtn, new_block, memory);
            },
            None => ()
        }
        None
    }

    fn parse_function(&'a self, function: &structs::Function, block: Block<'a>, memory: &mut Memory<'a>) {
        let return_type = match function.return_type {
            Some(ref data_type) => self.parse_datatype(data_type),
            None => self.context.new_int_type(4, true)
        };
        let aux = memory.function_scope.clone();
        memory.function_scope = function.name.clone();
        let mut arg_map = HashMap::new();
        let params = self.parse_args(&function.args);
        for i in 0..function.args.len() {
            let arg = &function.args[i];
            let param = params[i];
            arg_map.insert(arg.name.clone(), param);
        }
        memory.function_args.insert(function.name.clone(), arg_map);
        let new_function = self.context.new_function(None, gccjit::FunctionType::Internal, return_type, params.as_slice(), &function.name, false);
        memory.functions.insert(function.name.clone(), new_function);
        let new_block = new_function.new_block(&format!("{}_block", function.name));
        self.parse_block(&function.block, new_block, memory);
        memory.function_scope = aux;
    }

    fn parse_args(&'a self, args: &Vec<structs::Arg>) -> Vec<Parameter> {
        let mut params = Vec::new();
        for arg in args {
            let datatype = self.parse_datatype(&arg.datatype);
            let param = self.context.new_parameter(None, datatype, &arg.name);
            params.push(param);
        }
        params
    }

    fn parse_datatype(&'a self, datatype: &DataType) -> Type<'_> {
        let string_type = self.context.new_string_literal("test").get_type();
        match datatype {
            DataType::Bool => self.context.new_c_type(gccjit::CType::Bool),
            DataType::Float(bytecount) | DataType::Int(bytecount) => self.context.new_int_type(*bytecount as i32, true),
            DataType::UFloat(bytecount) | DataType::UInt(bytecount) => self.context.new_int_type(*bytecount as i32, false),
            DataType::String => string_type
        }
    }

    fn parse_if(&'a self, ast_if: &structs::If, block: Block<'a>, memory: &mut Memory<'a>) -> Block<'_> {
        let condition = self.parse_operation(&ast_if.condition, block, memory).unwrap();
        let function = block.get_function();
        let then_block = function.new_block("then_block");
        let else_block = function.new_block("else_block");
        self.parse_block(&ast_if.block, then_block, memory);
        block.end_with_conditional(None, condition, then_block, else_block);
        let mut else_should_continue = false;
        if let Some(ref otherwise) = ast_if.otherwise {
            match **otherwise {
                Otherwise::Block(ref block) => {
                    else_should_continue = block.box_return.is_none();
                    self.parse_block(block, else_block, memory);
                },
                _ => unreachable!()
            }
        }
        if ast_if.block.box_return.is_none() || else_should_continue {
            let continue_block = function.new_block("continue_block");
            if ast_if.block.box_return.is_none() {
                then_block.end_with_jump(None, continue_block);
            }
            if else_should_continue {
                else_block.end_with_jump(None, continue_block);
            }
            return continue_block;
        }
        else_block
    }

    fn parse_declaration(&'a self, declaration: &structs::Declaration, block: Block<'a>, memory: &mut Memory<'a>) {
        let mut value = self.parse_value(&declaration.value, block, memory).unwrap();
        let function = block.get_function();
        if let Some(ref dt) = declaration.datatype {
            let data_type = self.parse_datatype(dt);
            if !value.get_type().is_compatible_with(data_type) {
                value = self.context.new_cast(None, value, data_type);
            }
            let lvalue = function.new_local(None, data_type, &declaration.name);
            block.add_assignment(None, lvalue, value);
            memory.variables.insert(declaration.name.clone(), lvalue);
        }else{
            let lvalue = function.new_local(None, value.get_type(), &declaration.name);
            block.add_assignment(None, lvalue, value);
            memory.variables.insert(declaration.name.clone(), lvalue);
        }
    }

    fn parse_params(&'a self, args: &Vec<structs::Parameter>, block: Block<'a>, memory: &mut Memory<'a>) -> Vec<Option<RValue<'_>>> {
        use structs::Parameter;
        let mut params = Vec::new();
        for arg in args {
            let rvalue = match arg {
                Parameter::Name(name) => self.parse_name(name, memory, block),
                Parameter::Value(value) => self.parse_value(value, block, memory)
            };
            params.push(rvalue);
        }
        params
    }

    fn parse_call(&'a self, call: &structs::Call, block: Block<'a>, memory: &mut Memory<'a>) -> Option<RValue<'_>> {
        let function = memory.functions.get(&call.name).unwrap().clone();
        let mut args = self.parse_params(&call.args, block, memory).into_iter().map(|x| x.unwrap()).collect::<Vec<RValue>>();
        for i in 0..args.len() {
            let declared_type = function.get_param(i as i32).to_rvalue().get_type();
            if !declared_type.is_compatible_with(args[i].get_type()) {
                args[i] = self.context.new_cast(None, args[i], declared_type);
            }
        }
        Some(self.context.new_call(None, function, &args))
    }

    fn parse_operation(&'a self, operation: &Box<structs::Operation>, block: Block<'a>,memory: &mut Memory<'a>) -> Option<RValue<'_>> {
        use structs::Operation;
        match **operation {
            Operation::Atom(ref atom) => self.parse_atom(atom, block, memory),
            Operation::BinaryOp(ref binary_op) => self.parse_binary_op(binary_op, block, memory),
            Operation::UnaryOp(ref unary_op) => self.parse_unary_op(unary_op, block, memory)
        }
    }

    fn parse_binary_op(&'a  self, binary_op: &structs::BinaryOp, block: Block<'a>,memory: &mut Memory<'a>) -> Option<RValue<'_>> {
        use structs::Operations;

        let op = match binary_op.op {
            Operations::Add => Helper::Binary(gccjit::BinaryOp::Plus),
            Operations::Sub => Helper::Binary(gccjit::BinaryOp::Minus),
            Operations::Mul => Helper::Binary(gccjit::BinaryOp::Mult),
            Operations::Div => Helper::Binary(gccjit::BinaryOp::Divide),
            Operations::And => Helper::Binary(gccjit::BinaryOp::LogicalAnd),
            Operations::Or => Helper::Binary(gccjit::BinaryOp::LogicalOr),
            Operations::Lt => Helper::Comp(ComparisonOp::LessThan),
            Operations::Gt => Helper::Comp(ComparisonOp::GreaterThan),
            Operations::Lte => Helper::Comp(ComparisonOp::LessThanEquals),
            Operations::Gte => Helper::Comp(ComparisonOp::GreaterThanEquals),
            Operations::Eq => Helper::Comp(ComparisonOp::Equals),
            Operations::Neq => Helper::Comp(ComparisonOp::NotEquals),
            ref operation => unreachable!("Expected binary op or comparison op, found {:?}", operation)
        };
        let lhs = self.parse_operation(&binary_op.lhs, block, memory);
        let rhs = self.parse_operation(&binary_op.rhs, block, memory);
        match op {
            Helper::Binary(binary_op) => self.context.new_binary_op(None, binary_op, lhs.unwrap().get_type(), lhs.unwrap(), rhs.unwrap()).into(),
            Helper::Comp(comparison_op) => self.context.new_comparison(None, comparison_op, lhs.unwrap(), rhs.unwrap())
        }.into()
    }

    fn parse_unary_op(&'a self, unary_op: &structs::UnaryOp, block: Block<'a>,memory: &mut Memory<'a>) -> Option<RValue<'_>> {
        use structs::Operations;
        let op = match unary_op.prefix {
            Operations::Neg => UnaryOp::Minus,
            Operations::Not => UnaryOp::LogicalNegate,
            _ => todo!()
        };
        let rvalue = self.parse_operation(&unary_op.value, block, memory);
        match rvalue {
            Some(value) => {
                let data_type = value.get_type();
                Some(self.context.new_unary_op(None, op, data_type, value))
            },
            _ => panic!()
        }
    }

    fn parse_atom(&'a self, atom: &structs::Atom, block: Block<'a>, memory: &mut Memory<'a>) -> Option<RValue<'_>> {
        let rvalue = self.parse_value(&atom.value, block, memory);
        let mul = match atom.is_neg{
            true => Some((UnaryOp::Minus, UnaryOp::LogicalNegate)),
            false => None
        };
        match rvalue {
            Some(value) => {
                match mul {
                    Some(operations) => {
                        let data_type = value.get_type();
                        let bool_type = self.context.new_c_type(gccjit::CType::Bool);
                        if bool_type.is_compatible_with(data_type) {
                            return self.context.new_unary_op(None, operations.1, bool_type, value).into()
                        }else{
                            return self.context.new_unary_op(None, operations.0, data_type, value).into()
                        }
                    },
                    None => value.into()
                }
            },
            _ => panic!()
        }
    }

    fn parse_bool(&self, boolean: bool) -> Option<RValue<'_>> {
        let data_type = self.context.new_c_type(gccjit::CType::Bool);
        let bit = match boolean {
            true => 1,
            false => 0
        };
        Some(self.context.new_rvalue_from_int(data_type, bit))
    }

    fn parse_name(&self, name: &str, memory: &mut Memory<'a>, block: Block<'_>) -> Option<RValue<'_>> {
        if let Some(var) = memory.variables.get(name) {
            return Some(var.to_rvalue());
        }else if let Some(parameters) = memory.function_args.get(&memory.function_scope) {
            return Some(parameters.get(name).unwrap().to_rvalue());
        }else{
            panic!("porra fudeokkkkkkkk")
        }
    }

    fn parse_string(&self, string: &str) -> Option<RValue<'_>> {
        Some(self.context.new_string_literal(&string[1..string.len()-1]))
    }

    fn parse_int(&self, number: i32) -> Option<RValue<'_>> {
        let data_type = self.context.new_int_type(4, true);
        Some(self.context.new_rvalue_from_int(data_type, number))
    }

    fn parse_float(&self, number: f32) -> Option<RValue<'_>> {
        let data_type = self.context.new_int_type(4, true);
        Some(self.context.new_rvalue_from_double(data_type, number as f64))
    }
}
