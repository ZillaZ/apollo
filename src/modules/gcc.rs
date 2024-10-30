use gccjit::{
    BinaryOp, Block, ComparisonOp, Context, Function, LValue, Parameter, RValue, Struct, ToLValue,
    ToRValue, Type, Typeable, UnaryOp,
};
use std::borrow::BorrowMut;
use std::collections::HashMap;
use std::fmt::Pointer;
use std::rc::Rc;

use super::memory::{self, Memory};
use super::parser::Ast;
use super::structs::{
    self, AssignVar, Atom, Constructor, DataType, FieldAccessName, ForLoop, If, Impl, Name,
    Operation, Overloaded, OverloadedOp, Range, RangeValue, RefOp, StructDecl, Value,
};
use super::structs::{Expr, FunctionKind, LibLink, WhileLoop};
use crate::modules::structs::{Field, Otherwise, RangeType};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GccValues<'a> {
    L(LValue<'a>),
    R(RValue<'a>),
    Type(Type<'a>),
    Pair((Box<GccValues<'a>>, Box<GccValues<'a>>)),
    Nil,
}

impl<'a> GccValues<'a> {
    pub fn rvalue(&self) -> RValue<'a> {
        match self {
            GccValues::L(lvalue) => lvalue.to_rvalue(),
            GccValues::R(rvalue) => *rvalue,
            _ => unreachable!(),
        }
    }

    pub fn get_reference(&self) -> RValue<'a> {
        match self {
            GccValues::L(lvalue) => {
                let address = lvalue.get_address(None);
                address
            }
            GccValues::R(rvalue) => *rvalue,
            _ => unreachable!(),
        }
    }

    pub fn dereference(&self) -> LValue<'a> {
        match self {
            GccValues::L(lvalue) => *lvalue,
            GccValues::R(rvalue) => rvalue.dereference(None),
            _ => unreachable!(),
        }
    }

    pub fn binary_op(
        &self,
        r: GccValues<'a>,
        op: BinaryOp,
        context: &'a Context<'a>,
    ) -> GccValues<'a> {
        match (self, r) {
            (GccValues::L(left), GccValues::L(right)) => {
                let left = left.to_rvalue();
                let right = right.to_rvalue();
                let operation = context.new_binary_op(None, op, left.get_type(), left, right);
                GccValues::R(operation)
            }
            (GccValues::R(left), GccValues::R(right)) => {
                let operation = context.new_binary_op(None, op, left.get_type(), *left, right);
                GccValues::R(operation)
            }
            (GccValues::L(left), GccValues::R(right)) => {
                let operation =
                    context.new_binary_op(None, op, right.get_type(), left.to_rvalue(), right);
                GccValues::R(operation)
            }
            (GccValues::R(left), GccValues::L(right)) => {
                let operation =
                    context.new_binary_op(None, op, left.get_type(), *left, right.to_rvalue());
                GccValues::R(operation)
            }
            _ => unreachable!(),
        }
    }

    pub fn comparison_op(
        &self,
        r: GccValues<'a>,
        op: ComparisonOp,
        context: &'a Context<'a>,
    ) -> GccValues<'a> {
        match (self, r) {
            (GccValues::L(left), GccValues::L(right)) => {
                let left = left.to_rvalue();
                let right = right.to_rvalue();
                let operation = context.new_comparison(None, op, left, right);
                GccValues::R(operation)
            }
            (GccValues::R(left), GccValues::R(right)) => {
                let operation = context.new_comparison(None, op, *left, right);
                GccValues::R(operation)
            }
            (GccValues::L(left), GccValues::R(right)) => {
                let operation = context.new_comparison(None, op, left.to_rvalue(), right);
                GccValues::R(operation)
            }
            (GccValues::R(left), GccValues::L(right)) => {
                let operation = context.new_comparison(None, op, *left, right.to_rvalue());
                GccValues::R(operation)
            }
            (GccValues::Type(left), GccValues::Type(right)) => match op {
                ComparisonOp::Equals => {
                    let value = match left.is_compatible_with(right) {
                        true => 1,
                        false => 0,
                    };
                    let rvalue =
                        context.new_rvalue_from_int(<bool as Typeable>::get_type(context), value);
                    GccValues::R(rvalue)
                }
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }
}

pub enum Helper {
    Binary(BinaryOp),
    Comp(ComparisonOp),
}

pub struct GccContext<'a> {
    context: &'a Context<'a>,
}

impl<'a> GccContext<'a> {
    pub fn new(context: &'a Context<'a>) -> Self {
        Self { context }
    }

    fn gen_units(&'a self, memory: &mut Memory<'a>) {
        let int_type = memory.datatypes.get("i4").unwrap();
        let int_unit = self.context.new_rvalue_from_int(*int_type, 1);
        memory.units.insert(*int_type, int_unit);
        let char_type = memory.datatypes.get("char").unwrap();
        let char_unit = self.context.new_rvalue_from_int(*char_type, 1);
        memory.units.insert(*char_type, char_unit);
    }

    fn gen_numeric_types(&'a self, memory: &mut Memory<'a>) {
        let int_type = <i32 as Typeable>::get_type(self.context);
        let long_type = <i64 as Typeable>::get_type(self.context);
        let float_type = <f32 as Typeable>::get_type(self.context);
        let uint_type = <u32 as Typeable>::get_type(self.context);
        let ulong_type = <u64 as Typeable>::get_type(self.context);
        let ulong_int_type = self.context.new_c_type(gccjit::CType::UInt128t);
        memory.datatypes.insert("i4".into(), int_type);
        memory.datatypes.insert("i8".into(), long_type);
        memory.datatypes.insert("f4".into(), float_type);
        memory.datatypes.insert("u3".into(), uint_type);
        memory.datatypes.insert("u8".into(), ulong_type);
        memory.datatypes.insert("u16".into(), ulong_int_type);
    }

    fn is_pointer(&'a self, r#type: &Type<'a>, memory: &mut Memory<'a>) -> bool {
        memory.pointer_types.contains(r#type)
    }

    fn gen_text_types(&'a self, memory: &mut Memory<'a>) {
        let char_type = <char as Typeable>::get_type(self.context);
        let string_type = self.context.new_string_literal("").get_type();
        memory.datatypes.insert("char".into(), char_type);
        memory.datatypes.insert("string".into(), string_type);
        memory.pointer_types.insert(string_type.make_const());
        memory.pointer_types.insert(string_type);
    }

    fn gen_void_type(&'a self, memory: &mut Memory<'a>) {
        let void_ptr_type = <() as Typeable>::get_type(self.context).make_pointer();
        memory.datatypes.insert("Any".into(), void_ptr_type);
    }

    fn gen_primitive_types(&'a self, memory: &mut Memory<'a>) {
        self.gen_numeric_types(memory);
        self.gen_text_types(memory);
        self.gen_void_type(memory);
    }

    fn uuid(&'a self) -> String {
        uuid::Uuid::new_v4().to_string()
    }

    fn parse_expression(&'a self, ast: &Ast, memory: &mut Memory<'a>, block: &mut Block<'a>) {
        for expr in ast.expressions.iter() {
            let reference = &mut *memory;
            match expr {
                Expr::Return(ref rtn) => {
                    self.build_return(rtn, block, reference, ast);
                }
                Expr::Call(ref call) => {
                    let result = self.parse_call(call, None, block, reference, ast).rvalue();
                    block.add_eval(None, result);
                }
                Expr::Function(ref function) => {
                    self.parse_function(function, reference, ast);
                }
                Expr::Block(ref ast_block) => {
                    self.parse_block(ast_block, block, reference, ast);
                }
                Expr::Declaration(ref declaration) => {
                    self.parse_declaration(declaration, block, reference, ast);
                }
                Expr::If(ref ast_if) => {
                    *block = self.parse_if(ast_if, block, reference, ast);
                }
                Expr::Assignment(ref assignment) => {
                    self.parse_assignment(assignment, block, reference, ast);
                }
                Expr::Overloaded(ref overloaded) => {
                    self.parse_overloaded(overloaded, block, reference, ast);
                }
                Expr::StructDecl(ref r#struct) => {
                    self.parse_struct(r#struct, reference);
                }
                Expr::FieldAccess(ref access) => {
                    let value = self.parse_field_access(access, None, block, reference, ast);
                    block.add_eval(None, value.rvalue());
                }
                Expr::Trait(ref r#trait) => self.parse_trait(r#trait, block, reference),
                Expr::Link(ref lib_link) => self.add_link(lib_link),
                Expr::While(ref wl) => self.parse_while_loop(wl, block, ast, reference),
                Expr::For(fl) => self.parse_for_loop(&mut fl.clone(), block, ast, reference),
                Expr::Impl(implementation) => {
                    self.parse_impl(implementation, block, ast, reference)
                }
                _ => continue,
            }
        }
    }

    fn parse_impl(
        &'a self,
        implementation: &Impl,
        block: &mut Block<'a>,
        ast: &Ast,
        memory: &mut Memory<'a>,
    ) {
        self.parse_impl_block(implementation, ast, memory);
    }

    fn parse_impl_block(&'a self, implementation: &Impl, ast: &Ast, memory: &mut Memory<'a>) {
        for expr in implementation.block.expr.clone() {
            match *expr {
                Expr::Function(mut function) => {
                    let old = function.name.name.clone();
                    function.name.name = format!(
                        "{}{}{}",
                        implementation.trait_name, implementation.struct_name, function.name.name
                    );
                    self.parse_function(&function, memory, ast);
                    let function = memory.functions.get(&function.name.name).unwrap();
                    memory
                        .implementations
                        .insert(implementation.struct_name.clone(), *function);
                    let data_type = memory.datatypes.get(&implementation.struct_name).unwrap();
                    let entry = memory
                        .impls
                        .entry(*data_type)
                        .or_insert(vec![(old.clone(), *function)]);
                    if entry.iter().find(|(x, _)| x == old.as_str()).is_none() {
                        entry.push((old, *function));
                    }
                }
                _ => todo!(),
            }
        }
    }

    fn parse_for_loop(
        &'a self,
        fl: &mut ForLoop,
        block: &mut Block<'a>,
        ast: &Ast,
        memory: &mut Memory<'a>,
    ) {
        let function = block.get_function();
        let value = self.parse_value(&fl.range, block, memory, ast);
        let datatype = match value {
            GccValues::Pair((ref left, _)) => left.rvalue().get_type(),
            GccValues::L(val) => {
                let impls = memory.impls.get(&val.to_rvalue().get_type()).unwrap();
                impls
                    .iter()
                    .filter(|(x, _)| x == "peek")
                    .peekable()
                    .peek()
                    .unwrap()
                    .1
                    .get_return_type()
            }
            GccValues::R(val) => val.get_type(),
            _ => todo!(),
        };
        match value {
            GccValues::R(_) => {
                let (start, end) = match value {
                    GccValues::Pair((left, right)) => (left, right),
                    _ => todo!(),
                };
                println!("{:?} {:?}", start.rvalue(), end.rvalue());
                let pivot = function.new_local(None, datatype, fl.pivot.clone());
                memory
                    .variables
                    .get_mut(&memory.function_scope)
                    .unwrap()
                    .insert(fl.pivot.clone(), pivot);
                block.add_assignment(None, pivot, start.rvalue());
                let condition =
                    self.context
                        .new_comparison(None, ComparisonOp::Equals, pivot, end.rvalue());
                let mut loop_block = function.new_block(self.uuid());
                memory.blocks.insert(loop_block, false);
                let index = function.new_local(None, start.rvalue().get_type(), self.uuid());
                block.add_assignment(None, index, start.rvalue());
                println!("{:?}", memory.continue_block);
                let continue_block = function.new_block(self.uuid());
                let condition_block = function.new_block(self.uuid());
                condition_block.end_with_conditional(None, condition, continue_block, loop_block);
                loop_block.add_assignment_op(
                    None,
                    pivot,
                    BinaryOp::Plus,
                    memory.units.get(&datatype).unwrap().to_rvalue(),
                );
                memory.blocks.insert(condition_block, true);
                block.end_with_jump(None, condition_block);
                self.parse_block(&fl.block, &mut loop_block, memory, ast);
                memory.blocks.insert(loop_block, true);
                loop_block.end_with_jump(None, condition_block);
                *block = continue_block;
            }
            GccValues::L(value) => {
                let impls = memory.impls.get(&value.to_rvalue().get_type()).unwrap();
                let peek = impls.iter().find(|(x, _)| x == "peek").unwrap();
                let end = impls.iter().find(|(x, _)| x == "ended").unwrap();
                let start = self
                    .context
                    .new_call(None, peek.1, &[value.get_address(None)]);
                let end = self
                    .context
                    .new_call(None, end.1, &[value.get_address(None)]);
                let dt = <bool as Typeable>::get_type(self.context);
                let condition = self.context.new_comparison(
                    None,
                    ComparisonOp::Equals,
                    end,
                    self.context.new_rvalue_from_int(dt, 1),
                );
                let mut loop_block = function.new_block(self.uuid());
                memory.blocks.insert(loop_block, false);
                let pivot = function.new_local(None, start.get_type(), self.uuid());
                block.add_assignment(None, pivot, start);
                memory
                    .variables
                    .get_mut(&memory.function_scope)
                    .unwrap()
                    .insert(fl.pivot.clone(), pivot);
                println!("{:?}", memory.continue_block);
                let continue_block = function.new_block(self.uuid());
                let condition_block = function.new_block(self.uuid());
                condition_block.end_with_conditional(None, condition, continue_block, loop_block);
                println!("{:?}", impls);
                let next = impls.iter().find(|(x, _)| x == "next").unwrap();
                let next = self
                    .context
                    .new_call(None, next.1, &[value.get_address(None)]);
                loop_block.add_assignment(None, pivot, next);
                memory.blocks.insert(condition_block, true);
                block.end_with_jump(None, condition_block);
                self.parse_block(&fl.block, &mut loop_block, memory, ast);
                memory.blocks.insert(loop_block, true);
                loop_block.end_with_jump(None, condition_block);
                *block = continue_block
            }
            _ => todo!(),
        }
        memory.blocks.insert(*block, true);
    }

    fn parse_while_loop(
        &'a self,
        wl: &WhileLoop,
        block: &mut Block<'a>,
        ast: &Ast,
        memory: &mut Memory<'a>,
    ) {
        let active_function = block.get_function();
        let mut while_loop = active_function.new_block(self.uuid());
        block.end_with_jump(None, while_loop);
        let continue_block = active_function.new_block(self.uuid());
        *block = continue_block;
        let rtn = self.parse_block(&wl.block, &mut while_loop, memory, ast);
        let condition = self.parse_value(&wl.condition, block, memory, ast);
        if rtn != GccValues::Nil {
            panic!("Can't return inside of while loop. If you want to break early, use if.")
        }
        if let Some(last_block) = memory.last_block {
            while_loop.end_with_conditional(None, condition.rvalue(), last_block, continue_block);
        } else {
            while_loop.end_with_conditional(None, condition.rvalue(), while_loop, continue_block);
        }
    }

    fn add_link(&'a self, lib_link: &LibLink) {
        let (_, path) = std::env::vars().find(|(x, _)| x == "APOLLO_LIBS").unwrap();
        println!("{:?}", format!("-L{} -l:{}", path, lib_link.lib_name));
        if lib_link.lib_name.ends_with(".o") || lib_link.lib_name.ends_with(".a") {
            self.context
                .add_driver_option(format!("-L{} -l:{}", path, lib_link.lib_name));
        } else {
            self.context.add_driver_option(format!(
                "-l{}",
                lib_link.lib_name.split(".").peekable().peek().unwrap()
            ))
        }
    }

    fn setup_entry_point(&'a self, ast: &Ast, memory: &mut Memory<'a>) -> Block<'a> {
        self.gen_primitive_types(memory);
        self.gen_units(memory);
        self.add_builtin_functions(memory);
        self.build_imports(memory, ast);
        let dt = <i32 as Typeable>::get_type(&self.context);
        memory.variables.insert("main".into(), HashMap::new());
        let function = self.context.new_function(
            None,
            gccjit::FunctionType::Exported,
            dt,
            &[],
            &ast.namespace,
            false,
        );
        function.new_block("initial")
    }

    fn compile_program(&'a self) {
        self.context
            .set_optimization_level(gccjit::OptimizationLevel::Aggressive);
        self.context.set_program_name("apollo");
        self.context.dump_to_file("apollo.c", false);
        self.context
            .compile_to_file(gccjit::OutputKind::Executable, "apollo");
        self.context
            .compile_to_file(gccjit::OutputKind::DynamicLibrary, "apollo.so");
    }

    pub fn gen_bytecode(&'a self, ast: &Ast, memory: &mut Memory<'a>, should_compile: bool) {
        let mut block = self.setup_entry_point(ast, memory);
        self.parse_expression(ast, memory, &mut block);
        block.end_with_return(
            None,
            self.context
                .new_rvalue_from_int(<i32 as Typeable>::get_type(&self.context), 0),
        );

        if should_compile {
            self.compile_program();
        }
    }

    fn parse_trait(
        &'a self,
        r#trait: &structs::Trait,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
    ) {
        let mut fields = Vec::new();
        let mut struct_fields = Vec::new();
        let mut counter = 0;
        let mut new_struct = HashMap::new();
        for field in r#trait.fields.iter() {
            new_struct.insert(field.name.clone(), counter);
            counter += 1;
            let field_type = self.parse_datatype(&field.datatype.clone(), memory);
            let struct_field = self.context.new_field(None, field_type, &field.name);
            struct_fields.push(struct_field);
            fields.push((field.name.clone(), field_type));
        }
        let trait_type = self
            .context
            .new_struct_type(None, &r#trait.name, &struct_fields);
        memory
            .datatypes
            .insert(r#trait.name.clone(), trait_type.as_type());
        memory.structs.insert(trait_type, new_struct);
        memory
            .trait_types
            .insert(trait_type.as_type(), r#trait.name.clone());
        memory.traits.insert(r#trait.name.clone(), fields);
    }

    fn parse_struct(&'a self, r#struct: &StructDecl, memory: &mut Memory<'a>) {
        let mut fields = Vec::new();
        let mut counter = 0;
        let mut new_struct = HashMap::new();
        for r#trait in r#struct.traits.iter() {
            let trait_fields = memory.traits.get(r#trait).unwrap();
            for (field, datatype) in trait_fields.iter() {
                new_struct.insert(field.clone(), counter);
                let field = self.context.new_field(None, *datatype, field);
                fields.push(field);
                counter += 1;
            }
        }
        for field in r#struct.fields.iter() {
            new_struct.insert(field.name.clone(), counter);
            counter += 1;
            let field = self.parse_field(&field, memory);
            fields.push(field);
        }
        let struct_type =
            self.context
                .new_struct_type(None, r#struct.name.clone(), &fields.as_slice());
        memory.structs.insert(struct_type, new_struct);
        memory
            .datatypes
            .insert(r#struct.name.clone(), struct_type.as_type());
    }

    fn build_imports(&'a self, memory: &mut Memory<'a>, ast: &Ast) {
        let imports = &ast.imports;
        for (import, ast) in imports {
            let imported_ast = ast.clone();
            let mut new_memory = Memory::new(imported_ast.namespace.clone());
            self.gen_bytecode(&imported_ast, &mut new_memory, false);
            self.push_to_module(&import, memory, &mut new_memory);
        }
    }

    fn push_to_module(
        &'a self,
        import: &structs::Import,
        memory: &mut Memory<'a>,
        new_memory: &mut Memory<'a>,
    ) {
        if import.imported.is_empty() {
            let base_name = import.name.split("::").last().unwrap();
            new_memory.functions.iter().for_each(|(name, function)| {
                memory
                    .functions
                    .insert(format!("{}::{}", base_name, name), *function);
            });
            new_memory.structs.iter().for_each(|(r#struct, fields)| {
                memory.structs.insert(*r#struct, fields.clone());
            });
            new_memory.traits.iter().for_each(|(name, fields)| {
                memory
                    .traits
                    .insert(format!("{}->{}", base_name, name), fields.clone());
            });
            new_memory.trait_types.iter().for_each(|(types, name)| {
                memory
                    .trait_types
                    .insert(*types, format!("{}->{}", base_name, name));
            });
            new_memory.datatypes.iter().for_each(|(name, datatype)| {
                memory
                    .datatypes
                    .insert(format!("{}->{}", base_name, name), *datatype);
            });
        } else {
            import.imported.iter().for_each(|name| {
                let pair = name.split("/").collect::<Vec<_>>();
                let kind = pair[0];
                let name = pair[1];
                match kind {
                    "struct" => {
                        let value = new_memory.datatypes.get(name).unwrap();
                        let other = new_memory.structs.get(&value.is_struct().unwrap()).unwrap();
                        memory.datatypes.insert(name.to_string(), *value);
                        memory
                            .structs
                            .insert(value.is_struct().unwrap(), other.clone());
                    }
                    "function" => {
                        let function = new_memory.functions.get(name).unwrap();
                        memory.functions.insert(name.to_string(), *function);
                    }
                    "trait" => {
                        let trait_type = new_memory.datatypes.get(name).unwrap();
                        let struct_type = new_memory
                            .structs
                            .get(&trait_type.is_struct().unwrap())
                            .unwrap();
                        let name = new_memory.trait_types.get(trait_type).unwrap();
                        let fields = new_memory.traits.get(name).unwrap();
                        memory.datatypes.insert(name.clone(), *trait_type);
                        memory
                            .structs
                            .insert(trait_type.is_struct().unwrap(), struct_type.clone());
                        memory.trait_types.insert(*trait_type, name.clone());
                        memory.traits.insert(name.clone(), fields.to_vec());
                    }
                    _ => unreachable!(),
                }
            });
        }
    }

    fn parse_overloaded(
        &'a self,
        overloaded: &Overloaded,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &Ast,
    ) {
        let lhs = match overloaded.lhs {
            structs::OverloadedLHS::FieldAccess(ref access) => {
                self.parse_field_access(access, None, block, memory, ast)
            }
            structs::OverloadedLHS::Name(ref name) => self.parse_name(name, memory, block),
        };
        let op = match overloaded.op {
            OverloadedOp::Add => BinaryOp::Plus,
            OverloadedOp::Sub => BinaryOp::Minus,
            OverloadedOp::Mul => BinaryOp::Mult,
            OverloadedOp::Div => BinaryOp::Divide,
        };
        let rhs = self.parse_value(&overloaded.rhs, block, memory, ast);
        block.add_assignment_op(None, lhs.dereference(), op, rhs.rvalue());
    }

    fn parse_assignment(
        &'a self,
        assignment: &structs::Assignment,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &Ast,
    ) {
        match assignment.var {
            AssignVar::Access(ref access) => {
                let var = self
                    .parse_array_access(access, block, memory, ast)
                    .dereference();
                let value = self.parse_value(&assignment.value, block, memory, ast);

                let value = self.new_cast(var.to_rvalue().get_type(), &value, memory);
                block.add_assignment(None, var, value.to_rvalue());
            }
            AssignVar::Name(ref name) => {
                let var = self.parse_name(name, memory, block).dereference();
                let value = self.parse_value(&assignment.value, block, memory, ast);
                let value = self.new_cast(var.to_rvalue().get_type(), &value, memory);
                block.add_assignment(None, var, value);
            }
            AssignVar::FieldAccess(ref access) => {
                let var = self
                    .parse_field_access(access, None, block, memory, ast)
                    .dereference();
                let value = self.parse_value(&assignment.value, block, memory, ast);
                let value = self.new_cast(var.to_rvalue().get_type(), &value, memory);
                block.add_assignment(None, var, value);
            }
        };
    }

    fn add_builtin_functions(&'a self, memory: &mut Memory<'a>) {
        for i in 0..memory.builtins.len() {
            let name = &memory.builtins[i];
            if name == "printf" {
                let format = self.context.new_parameter(
                    None,
                    self.context.new_c_type(gccjit::CType::ConstCharPtr),
                    "format",
                );
                let function = self.context.new_function(
                    None,
                    gccjit::FunctionType::Extern,
                    <i32 as Typeable>::get_type(&self.context),
                    &[format],
                    "printf",
                    true,
                );
                memory.functions.insert(name.clone(), function);
            } else {
                let function = self.context.get_builtin_function(name);
                memory.functions.insert(name.clone(), function);
            }
        }
    }

    fn build_return(
        &'a self,
        rtn: &structs::Return,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &Ast,
    ) {
        if let Some(ref value) = rtn.value {
            let mut value = self.parse_value(value, block, memory, ast).rvalue();
            let function_return_type = block.get_function().get_return_type();
            if !function_return_type.is_compatible_with(value.get_type()) {
                value = self.context.new_cast(None, value, function_return_type);
            }
            block.end_with_return(None, value);
        } else {
            block.end_with_void_return(None);
        }
    }

    fn parse_value(
        &'a self,
        value: &structs::Value,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &Ast,
    ) -> GccValues<'a> {
        let rtn = match value {
            Value::Int(number) => self.parse_int(*number),
            Value::UInt(number) => self.parse_uint(*number),
            Value::Float(number) => self.parse_float(*number),
            Value::String(ref string) => self.parse_string(string),
            Value::Name(ref name) => self.parse_name(name, memory, block),
            Value::Bool(boolean) => self.parse_bool(*boolean),
            Value::Atom(ref atom) => self.parse_atom(atom, block, memory, ast),
            Value::Operation(operation) => self.parse_operation(operation, block, memory, ast),
            Value::Call(call) => self.parse_call(call, None, block, memory, ast),
            Value::Block(ref ast_block) => {
                let variables = memory.variables.get(&memory.function_scope).unwrap();
                let args: Vec<(String, RValue<'a>)> = variables
                    .iter()
                    .map(|x| (x.0.clone(), x.1.to_rvalue()))
                    .collect();
                let params: Vec<Parameter<'a>> = args
                    .iter()
                    .map(|x| {
                        self.context
                            .new_parameter(None, x.1.get_type(), x.0.clone())
                    })
                    .collect();
                if let Some(ref value) = ast_block.box_return {
                    let return_value = self
                        .parse_value(&value.value.as_ref().unwrap(), block, memory, ast)
                        .rvalue();
                    let name = format!("anon_{}", memory.anon_count);
                    memory.anon_count += 1;
                    let function = self.context.new_function(
                        None,
                        gccjit::FunctionType::Internal,
                        return_value.get_type(),
                        params.as_slice(),
                        &name,
                        false,
                    );
                    let mut new_block = function.new_block("anon_block");
                    memory.functions.insert(name.clone(), function);
                    self.parse_block(ast_block, &mut new_block, memory, ast);
                    GccValues::R(self.context.new_call(
                        None,
                        function,
                        args.iter().map(|x| x.1).collect::<Vec<_>>().as_slice(),
                    ))
                } else {
                    panic!("Block as value with no return is invalid!");
                }
            }
            Value::Array(ref array) => self.parse_array(array, block, memory, ast),
            Value::ArrayAccess(ref access) => {
                let lvalue = self.parse_array_access(access, block, memory, ast);
                lvalue
            }
            Value::Char(ref r#char) => self.parse_char(char),
            Value::Constructor(ref constructor) => {
                self.parse_constructor(constructor, block, memory, ast)
            }
            Value::FieldAccess(ref access) => {
                self.parse_field_access(access, None, block, memory, ast)
            }
            Value::Casting((ref value, ref target)) => {
                let value = self.parse_value(&value, block, memory, ast);
                let target = memory.datatypes.get(target.trim()).unwrap();
                GccValues::R(self.new_cast(*target, &value, memory))
            }
            Value::Range(ref range) => self.parse_range(range, block, memory, ast),
            _ => todo!(),
        };

        rtn
    }

    fn parse_range(
        &'a self,
        range: &RangeValue,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &Ast,
    ) -> GccValues<'a> {
        match range {
            RangeValue::Iterable(ref value) => self.parse_value(value, block, memory, ast),
            RangeValue::Range(ref range) => {
                let start = self.parse_value(&range.start, block, memory, ast);
                let end = self.parse_value(&range.end, block, memory, ast);
                match range.range_type {
                    RangeType::Exclusive => GccValues::Pair((Box::new(start), Box::new(end))),
                    RangeType::Inclusive => {
                        let end = self.context.new_binary_op(
                            None,
                            BinaryOp::Plus,
                            end.rvalue().get_type(),
                            end.rvalue(),
                            self.context.new_rvalue_from_int(end.rvalue().get_type(), 1),
                        );
                        GccValues::Pair((Box::new(start), Box::new(GccValues::R(end))))
                    }
                }
            }
        }
    }

    fn parse_field_access(
        &'a self,
        access: &structs::FieldAccess,
        aux: Option<GccValues<'a>>,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &Ast,
    ) -> GccValues<'a> {
        let value = self.parse_field_access_name(&access.name, aux, block, memory, ast);
        if let Some(ref next) = access.next {
            return self.parse_field_access(&next, Some(value), block, memory, ast);
        }
        value
    }

    fn parse_field_access_name(
        &'a self,
        name: &FieldAccessName,
        aux: Option<GccValues<'a>>,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &Ast,
    ) -> GccValues<'a> {
        match name {
            FieldAccessName::Name(ref name) => match aux {
                Some(val) => {
                    println!("some");
                    let mut value = if let Some(field) = val.rvalue().get_type().is_struct() {
                        println!("here");
                        let struct_fields = memory.structs.get(&field).unwrap();
                        let field_index = struct_fields.get(&name.name).unwrap();
                        let field = field.get_field(*field_index);
                        GccValues::R(val.dereference().access_field(None, field).to_rvalue())
                    } else if let Some(field) = val
                        .rvalue()
                        .dereference(None)
                        .to_rvalue()
                        .get_type()
                        .is_struct()
                    {
                        let struct_fields = memory.structs.get(&field).unwrap();
                        let field_index = struct_fields.get(&name.name).unwrap();
                        let field = field.get_field(*field_index);
                        GccValues::R(
                            val.rvalue()
                                .dereference(None)
                                .access_field(None, field)
                                .to_rvalue(),
                        )
                    } else {
                        panic!("xiiikk")
                    };
                    for _ in 0..name.op_count {
                        value = match name.op {
                            Some(RefOp::Reference) => GccValues::R(value.get_reference()),
                            Some(RefOp::Dereference) => GccValues::L(value.dereference()),
                            None => value,
                        };
                    }
                    value
                }
                None => {
                    let var = memory
                        .variables
                        .get(&memory.function_scope)
                        .unwrap()
                        .get(&name.name)
                        .unwrap();
                    match name.op {
                        Some(RefOp::Reference) => GccValues::R(var.get_address(None)),
                        Some(RefOp::Dereference) => GccValues::R(var.to_rvalue()),
                        None => GccValues::L(var.to_lvalue()),
                    }
                }
            },
            FieldAccessName::Call(ref call) => match aux {
                Some(val) => self.parse_call(call, Some(val), block, memory, ast),
                None => self.parse_call(call, None, block, memory, ast),
            },
            FieldAccessName::ArrayAccess(ref access) => match aux {
                Some(val) => {
                    if let Value::Name(ref name) = access.value {
                        let lvalue = self.parse_field_access_name(
                            &FieldAccessName::Name(name.clone()),
                            Some(val),
                            block,
                            memory,
                            ast,
                        );
                        let index = self.parse_value(&access.index, block, memory, ast);
                        GccValues::L(self.context.new_array_access(
                            None,
                            lvalue.rvalue(),
                            index.rvalue(),
                        ))
                    } else {
                        panic!("sexo 2 is realkkkk");
                    }
                }
                None => self.parse_array_access(access, block, memory, ast),
            },
        }
    }

    fn parse_constructor(
        &'a self,
        constructor: &Constructor,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &Ast,
    ) -> GccValues<'a> {
        //let decl = self.ast_context.structs.get(&constructor.name).unwrap();
        let mut values = Vec::new();
        for field in constructor.fields.iter() {
            let value = self
                .parse_params(&vec![field.value.clone()], block, memory, ast)
                .first()
                .unwrap()
                .rvalue();
            values.push(value);
        }
        let struct_type = memory.datatypes.get(&constructor.name).unwrap();
        GccValues::R(self.context.new_struct_constructor(
            None,
            *struct_type,
            None,
            values.as_slice(),
        ))
    }

    fn parse_field(
        &'a self,
        field: &structs::FieldDecl,
        memory: &mut Memory<'a>,
    ) -> gccjit::Field<'a> {
        let datatype = self.parse_datatype(&field.datatype, memory);
        self.context.new_field(None, datatype, field.name.clone())
    }

    fn parse_char(&'a self, c: &char) -> GccValues<'a> {
        GccValues::R(self.context.new_rvalue_from_int(
            <char as Typeable>::get_type(&self.context),
            *c.to_string().bytes().peekable().peek().unwrap() as i32,
        ))
    }

    fn parse_array_access(
        &'a self,
        access: &structs::ArrayAccess,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &Ast,
    ) -> GccValues<'a> {
        let rvalue = self.parse_value(&access.value, block, memory, ast).rvalue();
        let index = self.parse_value(&access.index, block, memory, ast).rvalue();
        GccValues::L(self.context.new_array_access(None, rvalue, index))
    }

    fn parse_array(
        &'a self,
        array: &structs::Array,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &Ast,
    ) -> GccValues<'a> {
        let data_type = self.parse_datatype(&array.array_type.data_type, memory);
        let array_type = match array.array_type.size.clone() {
            Value::Operation(op) => match (*op).clone() {
                Operation::Atom(atom) => match atom.value {
                    Value::Int(size) => self.context.new_array_type(None, data_type, size as u64),
                    _ => todo!(),
                },
                _ => todo!(),
            },
            _ => {
                todo!();
            }
        };
        let mut elements = Vec::new();
        for i in 0..array.elements.len() {
            let element = self
                .parse_value(&array.elements[i], block, memory, ast)
                .rvalue();
            elements.push(element);
        }
        let array = self
            .context
            .new_array_constructor(None, array_type, elements.as_slice());
        GccValues::R(array)
    }

    fn parse_block(
        &'a self,
        ast_block: &structs::Block,
        new_block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &Ast,
    ) -> GccValues<'a> {
        self.parse_expression(&ast_block.to_ast(), memory, new_block);
        if let Some(ref rtn) = ast_block.box_return {
            self.build_return(rtn, new_block, memory, ast);
            return GccValues::R(
                self.context
                    .new_rvalue_from_int(<i32 as Typeable>::get_type(&self.context), 0),
            );
        }
        GccValues::Nil
    }

    fn setup_function_args(
        &'a self,
        function: &structs::Function,
        memory: &mut Memory<'a>,
    ) -> Vec<Parameter<'a>> {
        let mut arg_map = HashMap::new();
        let params = self.parse_args(&function.args, memory);
        for i in 0..function.args.len() {
            let arg = &function.args[i];
            let param = params[i];
            arg_map.insert(arg.name.name.clone(), param);
        }
        let other_map = arg_map
            .iter()
            .map(|x| (x.0.clone(), x.1.to_lvalue()))
            .collect::<_>();
        memory
            .variables
            .insert(function.name.name.clone(), other_map);
        params
    }

    fn parse_native_function(
        &'a self,
        function: &structs::Function,
        memory: &mut Memory<'a>,
        ast: &Ast,
    ) {
        if memory.functions.contains_key(&function.name.name) {
            return;
        }
        let return_type = match function.return_type {
            Some(ref data_type) => self.parse_datatype(data_type, memory),
            None => <() as Typeable>::get_type(&self.context),
        };
        let aux = memory.function_scope.clone();
        memory.function_scope = function.name.name.clone();
        let function_kind = function.kind.to_gcc_type();
        let params = self.setup_function_args(function, memory);
        let new_function = self.context.new_function(
            None,
            function_kind,
            return_type,
            params.as_slice(),
            &function.name.name,
            false,
        );
        memory
            .function_addresses
            .insert(function.name.name.clone(), new_function.get_address(None));
        memory
            .functions
            .insert(function.name.name.clone(), new_function);
        let mut new_block = new_function.new_block(&format!("{}_block", function.name.name));
        self.parse_block(&function.block, &mut new_block, memory, ast);
        memory.function_scope = aux;
    }

    fn parse_external_function(&'a self, function: &structs::Function, memory: &mut Memory<'a>) {
        if memory.functions.contains_key(&function.name.name) {
            return;
        }
        let return_type = match function.return_type {
            Some(ref data_type) => self.parse_datatype(data_type, memory),
            None => <() as Typeable>::get_type(&self.context),
        };
        let function_kind = function.kind.to_gcc_type();
        let params = self.setup_function_args(function, memory);
        let new_function = self.context.new_function(
            None,
            function_kind,
            return_type,
            params.as_slice(),
            &function.name.name,
            false,
        );
        memory
            .function_addresses
            .insert(function.name.name.clone(), new_function.get_address(None));
        memory
            .functions
            .insert(function.name.name.clone(), new_function);
    }

    fn parse_function(&'a self, function: &structs::Function, memory: &mut Memory<'a>, ast: &Ast) {
        match function.kind {
            FunctionKind::Native | FunctionKind::Exported => {
                self.parse_native_function(function, memory, ast)
            }
            FunctionKind::External => self.parse_external_function(function, memory),
        }
    }

    fn parse_args(&'a self, args: &Vec<structs::Arg>, memory: &mut Memory<'a>) -> Vec<Parameter> {
        let mut params = Vec::new();
        for arg in args {
            let datatype = match arg.datatype.datatype {
                DataType::Array(ref array_type) => {
                    let element_type = self.parse_datatype(&array_type.data_type, memory);
                    element_type.make_pointer()
                }
                _ => self.parse_datatype(&arg.datatype, memory),
            };
            let param = self.context.new_parameter(None, datatype, &arg.name.name);
            params.push(param);
        }
        params
    }

    fn parse_datatype(&'a self, datatype: &structs::Type, memory: &mut Memory<'a>) -> Type<'_> {
        let r#type = match &datatype.datatype {
            DataType::Bool => <bool as Typeable>::get_type(&self.context),
            DataType::Int(bytecount) => *memory.datatypes.get(&format!("i{}", bytecount)).unwrap(),
            DataType::UInt(bytecount) => *memory.datatypes.get(&format!("u{}", bytecount)).unwrap(),
            DataType::Array(array_type) => {
                let element_type = self.parse_datatype(&array_type.data_type, memory);
                match array_type.size.clone() {
                    Value::Operation(op) => match (*op).clone() {
                        Operation::Atom(atom) => match atom.value {
                            Value::Int(size) => {
                                self.context.new_array_type(None, element_type, size as u64)
                            }
                            _ => todo!(),
                        },
                        _ => todo!(),
                    },
                    Value::Int(size) => {
                        self.context.new_array_type(None, element_type, size as u64)
                    }
                    _ => {
                        todo!();
                    }
                }
            }
            DataType::String => *memory.datatypes.get("string").unwrap(),
            DataType::Char => <char as Typeable>::get_type(&self.context),
            DataType::StructType(ref name) => {
                *if let Some(val) = memory.datatypes.get(name) {
                    val
                } else {
                    panic!("{name}")
                }
            }
            DataType::Float(_bytecount) => <f32 as Typeable>::get_type(&self.context),
            DataType::Trait(ref name) => *memory.datatypes.get(name).unwrap(),
            DataType::Any => <() as Typeable>::get_type(&self.context).make_pointer(),
            _ => unreachable!(),
        };
        if datatype.is_ref {
            let mut dt = r#type.make_pointer();
            for _ in 0..datatype.ref_count - 1 {
                dt = r#type.make_pointer();
            }
            dt
        } else {
            r#type
        }
    }

    fn parse_if(
        &'a self,
        ast_if: &structs::If,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &Ast,
    ) -> Block<'_> {
        let mut condition = self
            .parse_operation(&ast_if.condition, block, memory, ast)
            .rvalue();
        if ast_if.not {
            condition = self.context.new_unary_op(
                None,
                UnaryOp::LogicalNegate,
                condition.get_type(),
                condition,
            );
        }
        let function = block.get_function();
        let mut then_block = function.new_block(self.uuid());
        let mut else_block = function.new_block(self.uuid());
        self.parse_block(&ast_if.block, &mut then_block, memory, ast);
        block.end_with_conditional(None, condition, then_block, else_block);
        let mut else_should_continue = false;
        let mut else_exists = false;
        if let Some(ref otherwise) = ast_if.otherwise {
            else_exists = true;
            match **otherwise {
                Otherwise::Block(ref block) => {
                    else_should_continue = block.box_return.is_none();
                    self.parse_block(block, &mut else_block, memory, ast);
                }
                _ => unreachable!(),
            }
        }
        if ast_if.block.box_return.is_none() || else_should_continue {
            let continue_block = function.new_block(self.uuid());
            memory.last_block = Some(*block);
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

    fn parse_declaration(
        &'a self,
        declaration: &structs::Declaration,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &Ast,
    ) {
        match declaration.value {
            Some(Value::Constructor(ref constructor)) => {
                let mut map = HashMap::new();
                map.insert(declaration.name.name.clone(), constructor.name.clone());
                memory
                    .constructors
                    .insert(memory.function_scope.clone(), map);
            }
            Some(Value::Call(ref call)) => {
                if let Some(function) = ast.context.functions.get(&call.name.name) {
                    if let Some(ref function_return) = function.return_type {
                        if let DataType::StructType(ref name) = function_return.datatype {
                            let mut map = HashMap::new();
                            map.insert(declaration.name.name.clone(), name.clone());
                            memory
                                .constructors
                                .insert(memory.function_scope.clone(), map);
                        }
                    }
                }
            }
            _ => (),
        };
        let value = if let Some(ref value) = declaration.value {
            Some(self.parse_value(value, block, memory, ast))
        } else {
            None
        };
        let function = block.get_function();
        if let Some(ref dt) = declaration.datatype {
            let data_type = self.parse_datatype(dt, memory);
            let lvalue = function.new_local(None, data_type, &declaration.name.name);
            if value.is_some() {
                let value = self.new_cast(data_type, &value.unwrap(), memory);
                block.add_assignment(None, lvalue, value);
            }
            let variables = memory.variables.get_mut(&memory.function_scope).unwrap();
            variables.insert(declaration.name.name.clone(), lvalue);
        } else {
            let dt = memory.unconst_type(value.as_ref().unwrap().rvalue().get_type());
            let lvalue = function.new_local(None, dt, &declaration.name.name);
            block.add_assignment(None, lvalue, value.as_ref().unwrap().rvalue());
            let variables = memory.variables.get_mut(&memory.function_scope).unwrap();
            variables.insert(declaration.name.name.clone(), lvalue);
        }
    }

    fn parse_params(
        &'a self,
        args: &Vec<structs::Parameter>,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &Ast,
    ) -> Vec<GccValues<'_>> {
        use structs::Parameter;
        let mut params = Vec::new();
        for arg in args {
            let value = match arg {
                Parameter::Name(name) => self.parse_name(name, memory, block),
                Parameter::Value(value) => self.parse_value(value, block, memory, ast),
            };
            params.push(value);
        }
        params
    }

    fn parse_call(
        &'a self,
        call: &structs::Call,
        field: Option<GccValues<'a>>,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &Ast,
    ) -> GccValues<'a> {
        let mut args = self.parse_params(&call.args, block, memory, ast);
        if call.name.name == "typeof" {
            return GccValues::Type(args[0].rvalue().get_type());
        }
        if call.name.name == "is_struct" {
            let value = match args[0].rvalue().get_type().is_struct().is_some() {
                true => 1,
                false => 0,
            };
            let rvalue = self
                .context
                .new_rvalue_from_int(<bool as Typeable>::get_type(&self.context), value);
            return GccValues::R(rvalue);
        }
        if call.name.name == "field_count" {
            let datatype = match args[0] {
                GccValues::Type(datatype) => datatype,
                GccValues::R(rvalue) => rvalue.get_type(),
                GccValues::L(lvalue) => lvalue.to_rvalue().get_type(),
                _ => unreachable!(),
            };
            let fields = memory.structs.get(&datatype.is_struct().unwrap()).unwrap();
            let value = fields.len();
            let rvalue = self
                .context
                .new_rvalue_from_int(<i32 as Typeable>::get_type(&self.context), value as i32);
            return GccValues::R(rvalue);
        }
        if !memory.functions.contains_key(&call.name.name) {
            self.parse_function(
                ast.context.functions.get(&call.name.name).unwrap(),
                memory,
                ast,
            );
        }
        let function = memory.functions.get(&call.name.name).unwrap().clone();
        if let Some(field) = field {
            let dt = function.get_param(0).to_rvalue().get_type();
            let mut vec = Vec::new();
            if dt.is_compatible_with(<() as Typeable>::get_type(&self.context).make_pointer()) {
                vec.push(field);
            } else if dt.is_compatible_with(field.rvalue().get_type().make_pointer()) {
                vec.push(GccValues::R(field.get_reference()));
            } else {
                vec.push(GccValues::R(field.rvalue()));
            }
            vec.append(&mut args);
            args = vec;
        }
        let mut params = args.iter().map(|x| x.rvalue()).collect::<Vec<_>>();
        for i in 0..args.len() {
            if function.get_param_count() <= i {
                break;
            }
            let declared_type = function.get_param(i as i32).to_rvalue().get_type();
            let parameter = params.get_mut(i).unwrap();
            *parameter = self.new_cast(declared_type, &args[i], memory);
        }

        GccValues::R(self.context.new_call(None, function, &params))
    }

    fn new_cast(
        &'a self,
        left_type: Type<'a>,
        right: &GccValues<'a>,
        memory: &mut Memory<'a>,
    ) -> RValue<'a> {
        let mut rtn = right.rvalue();
        let name = memory.trait_types.get_mut(&left_type);

        if name.is_some() {
            let name = name.unwrap().clone();
            rtn = self.struct_to_trait(right.rvalue(), &name, left_type, memory);
        } else if !left_type.is_compatible_with(rtn.get_type())
            && left_type
                .is_compatible_with(<() as Typeable>::get_type(&self.context).make_pointer())
            && !self.is_pointer(&rtn.get_type(), memory)
        {
            rtn = self
                .context
                .new_cast(None, right.get_reference(), left_type);
        } else if !left_type.is_compatible_with(rtn.get_type()) {
            rtn = self.context.new_cast(None, rtn, left_type);
        }
        rtn
    }

    fn struct_to_trait(
        &'a self,
        value: RValue<'a>,
        name: &String,
        declared_type: Type<'a>,
        memory: &mut Memory<'a>,
    ) -> RValue<'a> {
        let struct_type = value.get_type().is_struct().unwrap();
        let struct_fields = memory.structs.get(&struct_type).unwrap();
        let trait_fields = memory.traits.get(name).unwrap();
        let mut values = Vec::new();
        for (field, _) in trait_fields {
            if let Some(index) = struct_fields.get(field) {
                let field = struct_type.get_field(*index);
                values.push(value.access_field(None, field));
            }
        }
        self.context
            .new_struct_constructor(None, declared_type, None, &values)
    }

    fn parse_operation(
        &'a self,
        operation: &Box<structs::Operation>,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &Ast,
    ) -> GccValues<'a> {
        use structs::Operation;
        match **operation {
            Operation::Atom(ref atom) => self.parse_atom(atom, block, memory, ast),
            Operation::BinaryOp(ref binary_op) => {
                self.parse_binary_op(binary_op, block, memory, ast)
            }
            Operation::UnaryOp(ref unary_op) => self.parse_unary_op(unary_op, block, memory, ast),
        }
    }

    fn parse_binary_op(
        &'a self,
        binary_op: &structs::BinaryOp,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &Ast,
    ) -> GccValues<'_> {
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
            ref operation => {
                unreachable!("Expected binary op or comparison op, found {:?}", operation)
            }
        };
        let lhs = self.parse_operation(&binary_op.lhs, block, memory, ast);
        let rhs = self.parse_operation(&binary_op.rhs, block, memory, ast);
        GccValues::R(match op {
            Helper::Binary(binary_op) => lhs.binary_op(rhs, binary_op, &self.context).rvalue(),
            Helper::Comp(comparison_op) => lhs
                .comparison_op(rhs, comparison_op, &self.context)
                .rvalue(),
        })
    }

    fn parse_unary_op(
        &'a self,
        unary_op: &structs::UnaryOp,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &Ast,
    ) -> GccValues<'_> {
        use structs::Operations;
        let op = match unary_op.prefix {
            Operations::Neg => UnaryOp::Minus,
            Operations::Not => UnaryOp::LogicalNegate,
            _ => todo!(),
        };
        let value = self
            .parse_operation(&unary_op.value, block, memory, ast)
            .rvalue();
        let data_type = value.get_type();
        GccValues::R(self.context.new_unary_op(None, op, data_type, value))
    }

    fn parse_atom(
        &'a self,
        atom: &structs::Atom,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &Ast,
    ) -> GccValues<'_> {
        let value = self.parse_value(&atom.value, block, memory, ast);
        let mul = match atom.is_neg {
            true => Some((UnaryOp::Minus, UnaryOp::LogicalNegate)),
            false => None,
        };
        match mul {
            Some(operations) => {
                let data_type = value.rvalue().get_type();
                let bool_type = <bool as Typeable>::get_type(&self.context);
                if bool_type.is_compatible_with(data_type) {
                    return GccValues::R(self.context.new_unary_op(
                        None,
                        operations.1,
                        bool_type,
                        value.rvalue(),
                    ));
                } else {
                    return GccValues::R(self.context.new_unary_op(
                        None,
                        operations.0,
                        data_type,
                        value.rvalue(),
                    ));
                }
            }
            None => value,
        }
    }

    fn parse_bool(&self, boolean: bool) -> GccValues<'_> {
        let data_type = <bool as Typeable>::get_type(&self.context);
        let bit = match boolean {
            true => 1,
            false => 0,
        };
        GccValues::R(self.context.new_rvalue_from_int(data_type, bit))
    }

    fn parse_name(
        &self,
        name: &Name,
        memory: &mut Memory<'a>,
        block: &mut Block<'a>,
    ) -> GccValues<'a> {
        let variables = memory.variables.get(&memory.function_scope).unwrap();
        if name.name[0..1] == name.name[0..1].to_uppercase() {
            let datatype = memory
                .datatypes
                .get(&name.name)
                .expect("Refered datatype does not exist");
            return GccValues::Type(*datatype);
        }
        let mut value = if let Some(var) = variables.get(&name.name) {
            self.access_name(var, name)
        } else if let Some(address) = memory.function_addresses.get(&name.name) {
            GccValues::R(*address)
        } else {
            panic!("Variable {} not found", name.name)
        };
        value
    }

    fn access_name(&self, var: &LValue<'a>, name: &Name) -> GccValues<'a> {
        let value = match name.op {
            Some(ref op) => {
                return match op {
                    RefOp::Reference => GccValues::R(var.get_address(None)),
                    RefOp::Dereference => GccValues::L(var.to_rvalue().dereference(None)),
                };
            }
            None => GccValues::L(*var),
        };
        return value;
    }

    fn parse_string(&self, string: &str) -> GccValues<'_> {
        let value = self
            .context
            .new_string_literal(&string[1..string.len() - 1]);
        GccValues::R(value)
    }

    fn parse_int(&self, number: i32) -> GccValues<'_> {
        let data_type = <i32 as Typeable>::get_type(&self.context);
        GccValues::R(self.context.new_rvalue_from_int(data_type, number))
    }

    fn parse_uint(&self, number: u32) -> GccValues<'_> {
        let data_type = <u32 as Typeable>::get_type(self.context);
        GccValues::R(self.context.new_rvalue_from_int(data_type, number as i32))
    }

    fn parse_float(&self, number: f32) -> GccValues<'_> {
        let data_type = <f32 as Typeable>::get_type(&self.context);
        GccValues::R(
            self.context
                .new_rvalue_from_double(data_type, number as f64),
        )
    }
}
