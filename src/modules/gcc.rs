use std::collections::HashMap;
use gccjit::{BinaryOp, Block, ComparisonOp, Context, Function, LValue, Parameter, RValue, ToLValue, ToRValue, Type, UnaryOp, Typeable};

use crate::modules::structs::Otherwise;
use super::ast_context::AstContext;
use super::structs::{self, AssignVar, DataType, Name, Overloaded, OverloadedOp, RefOp, Value};
use super::structs::Expr;

#[derive(Debug)]
pub enum GccValues<'a> {
    L(LValue<'a>),
    R(RValue<'a>),
    Nil
}

impl <'a>GccValues<'a> {
    pub fn rvalue(&self) -> RValue<'a> {
        match self {
            GccValues::L(lvalue) => lvalue.to_rvalue(),
            GccValues::R(rvalue) => *rvalue,
            _ => unreachable!()
        }
    }

    pub fn get_reference(&self) -> RValue<'a> {
        match self {
            GccValues::L(lvalue) => {
                let address = lvalue.get_address(None);
                address
            }
            GccValues::R(rvalue) => {
                
                *rvalue
            }
            _ => unreachable!()
        }
    }

    pub fn dereference(&self) -> LValue<'a> {
        match self {
            GccValues::L(lvalue) => *lvalue,
            GccValues::R(rvalue) => rvalue.dereference(None),
            _ => unreachable!()
        }
    }
}

pub enum Helper {
    Binary(BinaryOp),
    Comp(ComparisonOp)
}

pub struct Memory<'a> {
    pub variables: HashMap<String, HashMap<String, LValue<'a>>>,
    pub functions: HashMap<String, Function<'a>>,
    pub builtins: Vec<String>,
    pub function_scope: String,
    pub anon_count: u32
}

impl <'a>Memory<'a> {
    pub fn new() -> Self {
        let variables = HashMap::new();
        let functions = HashMap::new();
        let builtins = vec!["printf", "strnlen", "malloc"].iter().map(|x| x.to_string()).collect::<_>();
        let function_scope = "main".into();
        let anon_count = 0;
        Self { variables, functions, builtins, function_scope, anon_count }
    }
}

pub struct GccContext<'a> {
    context: Context<'a>,
    ast_context: AstContext,
}

impl<'a> GccContext<'a> {
    pub fn new(ast_context: AstContext) -> Self {
        let context = Context::default();
        context.set_optimization_level(gccjit::OptimizationLevel::Aggressive);
        Self { context, ast_context }
    }

    pub fn gen_bytecode(&'a self, mut memory: Memory<'a>, ast: &mut Vec<Expr>) {
        self.add_builtin_functions(&mut memory);
        let dt = <i32 as Typeable>::get_type(&self.context);
        memory.variables.insert("main".into(), HashMap::new());
        let function =
            self.context
                .new_function(None, gccjit::FunctionType::Exported, dt, &[], "main", false);
        let mut block = function.new_block("initial");

        for expr in ast {
            let reference = &mut memory;
            match expr {
                Expr::Return(ref rtn) =>  { self.build_return(rtn, block, reference); },
                Expr::Call(ref call) => {
                    let result = self.parse_call(call, block, reference).rvalue();
                    block.add_eval(None, result);
                },
                Expr::Function(ref function) => { self.parse_function(function, block, reference); },
                Expr::Block(ref ast_block) => { self.parse_block(ast_block, block, reference); },
                Expr::Declaration(ref declaration) => { self.parse_declaration(declaration, block, reference); },
                Expr::If(ref ast_if) => { block = self.parse_if(ast_if, block, reference); },
                Expr::Assignment(ref assignment) => { self.parse_assignment(assignment, block, reference); }
                Expr::Overloaded(ref overloaded) => { self.parse_overloaded(overloaded, block, reference); }
            }
        }
        self.context.dump_to_file("apollo.c", false);
        self.context.compile_to_file(gccjit::OutputKind::Executable, "apollo");
        self.context.compile_to_file(gccjit::OutputKind::Assembler, "apollo.s");
    }

    fn parse_overloaded(&'a self, overloaded: &Overloaded, block: Block<'a>, memory: &mut Memory<'a>) {
        let lhs = self.parse_name(&overloaded.lhs, memory, block);
        let op = match overloaded.op {
            OverloadedOp::Add => BinaryOp::Plus,
            OverloadedOp::Sub => BinaryOp::Minus,
            OverloadedOp::Mul => BinaryOp::Mult,
            OverloadedOp::Div => BinaryOp::Divide
        };
        let rhs = self.parse_value(&overloaded.rhs, block, memory);
        println!("parsing here");
        block.add_assignment_op(None, lhs.dereference(), op, rhs.rvalue());
    }

    fn parse_assignment(&'a self, assignment: &structs::Assignment, block: Block<'a>, memory: &mut Memory<'a>) {
        match assignment.var {
            AssignVar::Access(ref access) => {
                let var = self.parse_array_access(access, block, memory).dereference();
                let mut value = self.parse_value(&assignment.value, block, memory).rvalue();
                if !var.to_rvalue().get_type().is_compatible_with(value.get_type()) {
                    value = self.context.new_cast(None, value, var.to_rvalue().get_type());
                }
                block.add_assignment(None, var, value.to_rvalue());
            },
            AssignVar::Name(ref name) => {
                let var = self.parse_name(name, memory, block).dereference();
                let mut value = self.parse_value(&assignment.value, block, memory);
                if !var.to_rvalue().get_type().is_compatible_with(value.rvalue().get_type()) {
                    value = GccValues::R(self.context.new_cast(None, value.rvalue(), var.to_rvalue().get_type()));
                }
                block.add_assignment(None, var, value.rvalue());
            }
        };
    }

    fn add_builtin_functions(&'a self, memory: &mut Memory<'a>) {
        for i in 0..memory.builtins.len() {
            let name = &memory.builtins[i];
            let function = self.context.get_builtin_function(name);
            memory.functions.insert(name.clone(), function);
        }
    }

    fn build_return(&'a self, rtn: &structs::Return, block: Block<'a>, memory: &mut Memory<'a>) {
        if let Some(ref value) = rtn.value {
            let mut value = self.parse_value(value, block, memory).rvalue();
            let function_return_type = block.get_function().get_return_type();
            if !function_return_type.is_compatible_with(value.get_type()) {
                value = self.context.new_cast(None, value, function_return_type);
            }
            block.end_with_return(None, value);
        }else{
            block.end_with_void_return(None);
        }
    }

    fn parse_value(&'a self, value: &structs::Value, block: Block<'a>, memory: &mut Memory<'a>) -> GccValues<'a> {
        let rtn = match value {
            Value::Int(number) => self.parse_int(*number),
            Value::Float(number) => self.parse_float(*number),
            Value::String(ref string) => self.parse_string(string),
            Value::Name(ref name) => self.parse_name(name, memory, block),
            Value::Bool(boolean) => self.parse_bool(*boolean),
            Value::Atom(ref atom) => self.parse_atom(atom, block, memory),
            Value::Operation(operation) => self.parse_operation(operation, block, memory),
            Value::Call(call) => self.parse_call(call, block, memory),
            Value::Block(ref ast_block) => {
                let variables = memory.variables.get(&memory.function_scope).unwrap();
                let args : Vec<(String, RValue<'a>)> = variables.iter().map(|x| (x.0.clone(), x.1.to_rvalue())).collect();
                let params : Vec<Parameter<'a>> = args.iter().map(|x| self.context.new_parameter(None, x.1.get_type(), x.0.clone())).collect();
                if let Some(ref value) = ast_block.box_return {
                    let return_value = self.parse_value(&value.value.as_ref().unwrap(), block, memory).rvalue();
                    let name = format!("anon_{}", memory.anon_count);
                    memory.anon_count += 1;
                    let function = self.context.new_function(None, gccjit::FunctionType::Internal, return_value.get_type(), params.as_slice(), &name, false);
                    let new_block = function.new_block("anon_block");
                    memory.functions.insert(name.clone(), function);
                    self.parse_block(ast_block, new_block, memory);
                    GccValues::R(self.context.new_call(None, function, args.iter().map(|x| x.1).collect::<Vec<_>>().as_slice()))
                }else{
                    panic!("Block as value with no return is invalid!");
                }
            }
            Value::Array(ref array) => self.parse_array(array, block, memory),
            Value::ArrayAccess(ref access) => {
                let lvalue = self.parse_array_access(access, block, memory);
                GccValues::R(lvalue.rvalue())
            },
            Value::Char(ref r#char) => self.parse_char(char),
            _ => todo!()
        };
        
        rtn
    }

    fn parse_char(&'a self, c: &char) -> GccValues<'a> {
        GccValues::R(self.context.new_rvalue_from_int(<char as Typeable>::get_type(&self.context), *c.to_string().bytes().peekable().peek().unwrap() as i32))
    }

    fn parse_array_access(&'a self, access: &structs::ArrayAccess, block: Block<'a>, memory: &mut Memory<'a>) -> GccValues<'a> {
        let rvalue = self.parse_value(&access.value, block, memory).rvalue();
        let index = self.parse_value(&access.index, block, memory).rvalue();
        GccValues::L(self.context.new_array_access(None, rvalue, index))
    }

    fn parse_array(&'a self, array: &structs::Array, block: Block<'a>, memory: &mut Memory<'a>) -> GccValues<'a> {
        let data_type = self.parse_datatype(&array.array_type.data_type);
        let size = self.parse_value(&array.array_type.size, block, memory).rvalue();
        let malloc = memory.functions.get("malloc").unwrap();
        let size = self.context.new_cast(None, size, malloc.get_param(0).to_rvalue().get_type());
        let allocation = self.context.new_call(None, *malloc, &[size]);
        let allocation = self.context.new_cast(None, allocation, data_type.make_pointer());
        for i in 0..array.elements.len() {
            let access = self.context.new_array_access(None, allocation, self.context.new_rvalue_from_int(<i32 as Typeable>::get_type(&self.context), i as i32));
            let element = &array.elements[i];
            let element = self.parse_value(element, block, memory).rvalue();
            block.add_assignment(None, access, element);
        }
        GccValues::R(allocation)
    }

    fn parse_block(&'a self, ast_block: &structs::Block, mut new_block: Block<'a>, memory: &mut Memory<'a>) -> GccValues<'a> {
        for expr in ast_block.expr.iter() {
            match **expr {
                Expr::Block(ref ast_block) => { self.parse_block(&Box::new(ast_block), new_block, memory); },
                Expr::Call(ref call) => {
                    let result = self.parse_call(call, new_block, memory).rvalue();
                    new_block.add_eval(None, result);
                },
                Expr::Declaration(ref declaration) => { self.parse_declaration(declaration, new_block, memory); },
                Expr::Function(ref function) =>  { self.parse_function(function, new_block, memory); },
                Expr::If(ref ast_if) => { new_block = self.parse_if(ast_if, new_block, memory); },
                Expr::Assignment(ref assignment) => { self.parse_assignment(assignment, new_block, memory); },
                Expr::Overloaded(ref overloaded) => { self.parse_overloaded(overloaded, new_block, memory); }
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
        GccValues::Nil
    }

    fn parse_function(&'a self, function: &structs::Function, block: Block<'a>, memory: &mut Memory<'a>) {
        if memory.functions.contains_key(&function.name.name) {
            return
        }
        let return_type = match function.return_type {
            Some(ref data_type) => self.parse_datatype(data_type),
            None => <() as Typeable>::get_type(&self.context)
        };
        let aux = memory.function_scope.clone();
        memory.function_scope = function.name.name.clone();
        let mut arg_map = HashMap::new();
        let params = self.parse_args(&function.args);
        for i in 0..function.args.len() {
            let arg = &function.args[i];
            let param = params[i];
            arg_map.insert(arg.name.name.clone(), param);
        }
        let other_map = arg_map.iter().map(|x| (x.0.clone(), x.1.to_lvalue())).collect::<_>();
        memory.variables.insert(function.name.name.clone(), other_map);
        let new_function = self.context.new_function(None, gccjit::FunctionType::Internal, return_type, params.as_slice(), &function.name.name, false);
        memory.functions.insert(function.name.name.clone(), new_function);
        let new_block = new_function.new_block(&format!("{}_block", function.name.name));
        self.parse_block(&function.block, new_block, memory);
        memory.function_scope = aux;
    }

    fn parse_args(&'a self, args: &Vec<structs::Arg>) -> Vec<Parameter> {
        let mut params = Vec::new();
        for arg in args {
            let datatype = match arg.datatype {
                DataType::Array(ref array_type) => {
                    let element_type = self.parse_datatype(&array_type.data_type);
                    element_type.make_pointer()
                }
                _ => self.parse_datatype(&arg.datatype)
            };
            let param = self.context.new_parameter(None, datatype, &arg.name.name);
            params.push(param);
        }
        params
    }

    fn parse_datatype(&'a self, datatype: &DataType) -> Type<'_> {
        let string_type = self.context.new_string_literal("test").get_type();
        match datatype {
            DataType::Bool => <bool as Typeable>::get_type(&self.context),
            DataType::Float(bytecount) | DataType::Int(bytecount) => self.context.new_int_type(*bytecount as i32, true),
            DataType::UFloat(bytecount) | DataType::UInt(bytecount) => self.context.new_int_type(*bytecount as i32, false),
            DataType::Array(array_type) => {
                let element_type = self.parse_datatype(&array_type.data_type);
                element_type.make_pointer()
            },
            DataType::String => string_type,
            DataType::Char => <char as Typeable>::get_type(&self.context)
        }
    }

    fn parse_if(&'a self, ast_if: &structs::If, block: Block<'a>, memory: &mut Memory<'a>) -> Block<'_> {
        let condition = self.parse_operation(&ast_if.condition, block, memory).rvalue();
        let function = block.get_function();
        let then_block = function.new_block("then_block");
        let else_block = function.new_block("else_block");
        self.parse_block(&ast_if.block, then_block, memory);
        block.end_with_conditional(None, condition, then_block, else_block);
        let mut else_should_continue = false;
        let mut else_exists = false;
        if let Some(ref otherwise) = ast_if.otherwise {
            else_exists = true;
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
            if !else_exists || else_should_continue {
                else_block.end_with_jump(None, continue_block);
            }
            return continue_block;
        }
        else_block
    }

    fn parse_declaration(&'a self, declaration: &structs::Declaration, block: Block<'a>, memory: &mut Memory<'a>) {
        let mut value = self.parse_value(&declaration.value, block, memory).rvalue();
        let function = block.get_function();
        let variables = memory.variables.get_mut(&memory.function_scope).unwrap();
        if let Some(ref dt) = declaration.datatype {
            let data_type = self.parse_datatype(dt);
            if !value.get_type().is_compatible_with(data_type) {
                value = self.context.new_cast(None, value, data_type);
            }
            let lvalue = function.new_local(None, data_type, &declaration.name.name);
            block.add_assignment(None, lvalue, value);
            variables.insert(declaration.name.name.clone(), lvalue);
        }else{
            let lvalue = function.new_local(None, value.get_type(), &declaration.name.name);
            block.add_assignment(None, lvalue, value);
            variables.insert(declaration.name.name.clone(), lvalue);
        }
    }

    fn parse_params(&'a self, args: &Vec<structs::Parameter>, block: Block<'a>, memory: &mut Memory<'a>) -> Vec<GccValues<'_>> {
        use structs::Parameter;
        let mut params = Vec::new();
        for arg in args {
            let value = match arg {
                Parameter::Name(name) => self.parse_name(name, memory, block),
                Parameter::Value(value) => self.parse_value(value, block, memory)
            };
            params.push(value);
        }
        params
    }

    fn parse_call(&'a self, call: &structs::Call, block: Block<'a>, memory: &mut Memory<'a>) -> GccValues<'a> {
        if !memory.functions.contains_key(&call.name.name) {
            self.parse_function(self.ast_context.functions.get(&call.name.name).unwrap(), block, memory);
        }
        let function = memory.functions.get(&call.name.name).unwrap().clone();
        let mut args = self.parse_params(&call. args, block, memory).iter().map(|x| x.get_reference()).collect::<Vec<_>>();

        for i in 0..args.len() {
            let declared_type = function.get_param(i as i32).to_rvalue().get_type();
            if !declared_type.is_compatible_with(args[i].get_type()) {
                args[i] = self.context.new_cast(None, args[i], declared_type);
            }
        }
        GccValues::R(self.context.new_call(None, function, &args))
    }

    fn parse_operation(&'a self, operation: &Box<structs::Operation>, block: Block<'a>,memory: &mut Memory<'a>) -> GccValues<'a> {
        use structs::Operation;
        match **operation {
            Operation::Atom(ref atom) => self.parse_atom(atom, block, memory),
            Operation::BinaryOp(ref binary_op) => self.parse_binary_op(binary_op, block, memory),
            Operation::UnaryOp(ref unary_op) => self.parse_unary_op(unary_op, block, memory)
        }
    }

    fn parse_binary_op(&'a  self, binary_op: &structs::BinaryOp, block: Block<'a>,memory: &mut Memory<'a>) -> GccValues<'_> {
        use structs::Operations;

        let op = match binary_op.op {
            Operations::Add => Helper::Binary(gccjit::BinaryOp::Plus),
            Operations::Sub => Helper::Binary(gccjit::BinaryOp::Minus),
            Operations::Mul => Helper::Binary(gccjit::BinaryOp::Mult),
            Operations::Div => Helper::Binary(gccjit::BinaryOp::Divide),
            Operations::Modulo => Helper::Binary(BinaryOp::Modulo),
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
        GccValues::R(match op {
            Helper::Binary(binary_op) => self.context.new_binary_op(None, binary_op, lhs.rvalue().get_type(), lhs.rvalue(), rhs.rvalue()).into(),
            Helper::Comp(comparison_op) => self.context.new_comparison(None, comparison_op, lhs.rvalue(), rhs.rvalue())
        })
    }

    fn parse_unary_op(&'a self, unary_op: &structs::UnaryOp, block: Block<'a>,memory: &mut Memory<'a>) -> GccValues<'_> {
        use structs::Operations;
        let op = match unary_op.prefix {
            Operations::Neg => UnaryOp::Minus,
            Operations::Not => UnaryOp::LogicalNegate,
            _ => todo!()
        };
        let value = self.parse_operation(&unary_op.value, block, memory).rvalue();
        let data_type = value.get_type();
        GccValues::R(self.context.new_unary_op(None, op, data_type, value))
    }

    fn parse_atom(&'a self, atom: &structs::Atom, block: Block<'a>, memory: &mut Memory<'a>) -> GccValues<'_> {
        let value = self.parse_value(&atom.value, block, memory);
        let mul = match atom.is_neg{
            true => Some((UnaryOp::Minus, UnaryOp::LogicalNegate)),
            false => None
        };
        match mul {
            Some(operations) => {
                let data_type = value.rvalue().get_type();
                let bool_type = <bool as Typeable>::get_type(&self.context);
                if bool_type.is_compatible_with(data_type) {
                    return GccValues::R(self.context.new_unary_op(None, operations.1, bool_type, value.rvalue()))
                }else{
                    return GccValues::R(self.context.new_unary_op(None, operations.0, data_type, value.rvalue()))
                }
            },
            None => value
        }
    }

    fn parse_bool(&self, boolean: bool) -> GccValues<'_> {
        let data_type = <bool as Typeable>::get_type(&self.context);
        let bit = match boolean {
            true => 1,
            false => 0
        };
        GccValues::R(self.context.new_rvalue_from_int(data_type, bit))
    }

    fn parse_name(&self, name: &Name, memory: &mut Memory<'a>, block: Block<'_>) -> GccValues<'a> {
        let variables = memory.variables.get(&memory.function_scope).unwrap();
        if let Some(var) = variables.get(&name.name) {
            self.access_name(var, name)
        }else{
            panic!("Variable {} not found. Working on {}", name.name, memory.function_scope)
        }
    }

    fn access_name(&self, var: &LValue<'a>, name: &Name) -> GccValues<'a> {
        let value = match name.op {
            Some(ref op) => {
                return match op {
                    RefOp::Reference => GccValues::R(var.get_address(None)),
                    RefOp::Dereference => GccValues::R(var.to_rvalue())
                };
            },
            None => GccValues::R(var.to_rvalue())
        };
        return value;
    }

    fn parse_string(&self, string: &str) -> GccValues<'_> {
        GccValues::R(self.context.new_string_literal(&string[1..string.len()-1]))
    }

    fn parse_int(&self, number: i32) -> GccValues<'_> {
        let data_type = <i32 as Typeable>::get_type(&self.context);
        GccValues::R(self.context.new_rvalue_from_int(data_type, number))
    }

    fn parse_float(&self, number: f32) -> GccValues<'_> {
        let data_type = <f32 as Typeable>::get_type(&self.context);
        GccValues::R(self.context.new_rvalue_from_double(data_type, number as f64))
    }
}
