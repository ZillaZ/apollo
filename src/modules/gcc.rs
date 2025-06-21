use gccjit::{
    BinaryOp, Block, ComparisonOp, Context, LValue, Parameter, RValue, ToLValue, ToRValue, Type,
    Typeable, UnaryOp,
};
use uuid::Uuid;
use std::borrow::BorrowMut;
use std::cell::RefCell;
use std::collections::vec_deque::IterMut;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use super::memory::Memory;
use super::parser::Ast;
use super::structs::{
    self, AssignVar, Constructor, DataType, Enum, EnumValue, FieldAccessName, ForLoop, Impl, Name, Overloaded, OverloadedOp, RangeValue, RefOp, StructDecl, Value, ValueEnum
};
use super::structs::{Expr, FunctionKind, LibLink, WhileLoop};
use crate::modules::structs::{Otherwise, RangeType};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GccValues<'a> {
    L(LValue<'a>),
    R(RValue<'a>),
    Type(Type<'a>),
    Range(RValue<'a>),
    Nil,
}

impl<'a> GccValues<'a> {
    pub fn rvalue(&self) -> RValue<'a> {
        match self {
            GccValues::L(lvalue) => lvalue.to_rvalue(),
            GccValues::R(rvalue) | GccValues::Range(rvalue) => *rvalue,
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
    imports: HashSet<&'a str>,
    context: &'a Context<'a>,
}

impl<'a> GccContext<'a> {
    pub fn new(context: &'a Context<'a>) -> Self {
        let imports = HashSet::new();
        Self { imports, context }
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
        let int_1 = <i8 as Typeable>::get_type(self.context);
        let int_2 = <i16 as Typeable>::get_type(self.context);
        let int_4 = <i32 as Typeable>::get_type(self.context);
        let int_8 = <i64 as Typeable>::get_type(self.context);
        let float_4 = <f32 as Typeable>::get_type(self.context);
        let float_8 = <f64 as Typeable>::get_type(self.context);
        let uint_1 = <u8 as Typeable>::get_type(self.context);
        let uint_2 = <u16 as Typeable>::get_type(self.context);
        let uint_4 = <u32 as Typeable>::get_type(self.context);
        let uint_8 = <u64 as Typeable>::get_type(self.context);
        let uint_16 = self.context.new_c_type(gccjit::CType::UInt128t);
        let bool_type = <bool as Typeable>::get_type(self.context);
        memory.datatypes.insert("bool".into(), bool_type);
        memory.datatypes.insert("i1".into(), int_1);
        memory.datatypes.insert("i2".into(), int_2);
        memory.datatypes.insert("i4".into(), int_4);
        memory.datatypes.insert("i8".into(), int_8);
        memory.datatypes.insert("f4".into(), float_4);
        memory.datatypes.insert("f8".into(), float_8);
        memory.datatypes.insert("u1".into(), uint_1);
        memory.datatypes.insert("u2".into(), uint_2);
        memory.datatypes.insert("u4".into(), uint_4);
        memory.datatypes.insert("u8".into(), uint_8);
        memory.datatypes.insert("u16".into(), uint_16);
    }

    fn is_pointer(&'a self, r#type: &Type<'a>, memory: &mut Memory<'a>) -> bool {
        memory.pointer_types.contains(r#type)
    }

    fn gen_text_types(&'a self, memory: &mut Memory<'a>) {
        let char_type = <char as Typeable>::get_type(self.context);
        let string_val = self.context.new_string_literal("");
        let string_type = string_val.get_type();
        memory.datatypes.insert("char".into(), char_type);
        memory.datatypes.insert("string".into(), string_type);
        memory.pointer_types.insert(string_type.make_const());
        memory.pointer_types.insert(string_type);
    }

    fn gen_void_type(&'a self, memory: &mut Memory<'a>) {
        let void_ptr_type = <() as Typeable>::get_type(self.context).make_pointer();
        memory.pointer_types.insert(void_ptr_type);
        memory.datatypes.insert("Any".into(), void_ptr_type);
    }

    fn gen_custom_types(&'a self, memory: &mut Memory<'a>) {
        let range_type = memory.datatypes.get("i4").unwrap();
        let start = self.context.new_field(None, *range_type, "start");
        let end = self.context.new_field(None, *range_type, "end");
        let range = self.context.new_struct_type(None, "ApolloRange", &[start, end]);
        memory.datatypes.insert("range".into(), range.as_type());
    }

    fn gen_primitive_types(&'a self, memory: &mut Memory<'a>) {
        self.gen_numeric_types(memory);
        self.gen_text_types(memory);
        self.gen_void_type(memory);
        self.gen_custom_types(memory);
    }

    fn uuid(&'a self) -> String {
        uuid::Uuid::new_v4().to_string()
    }

    fn parse_expression(&'a self, ast: &mut Ast, memory: &mut Memory<'a>, block: &mut Block<'a>) {
        for expr in ast.expressions.clone().iter_mut() {
            let reference = &mut *memory;
            match expr {
                Expr::Return(ref mut rtn) => {
                    self.build_return(rtn, block, reference, ast);
                }
                Expr::Call(ref mut call) => {
                    let result = self.parse_call(call, None, block, reference, ast).rvalue();
                    block.add_eval(None, result);
                }
                Expr::Function(ref mut function) => {
                    self.parse_function(function, reference, ast);
                }
                Expr::Block(ref mut ast_block) => {
                    self.parse_block(ast_block, block, reference, ast);
                }
                Expr::Declaration(ref mut declaration) => {
                    self.parse_declaration(declaration, block, reference, ast);
                }
                Expr::If(ref mut ast_if) => {
                    *block = self.parse_if(ast_if, block, reference, ast);
                }
                Expr::Assignment(ref mut assignment) => {
                    self.parse_assignment(assignment, block, reference, ast);
                }
                Expr::Overloaded(ref mut overloaded) => {
                    self.parse_overloaded(overloaded, block, reference, ast);
                }
                Expr::StructDecl(ref mut r#struct) => {
                    self.parse_struct(r#struct, reference);
                }
                Expr::FieldAccess(ref mut access) => {
                    let value = self.parse_field_access(access, None, block, reference, ast);
                    block.add_eval(None, value.rvalue());
                }
                Expr::Trait(ref mut r#trait) => self.parse_trait(r#trait, block, reference),
                Expr::Link(ref lib_link) => self.add_link(lib_link),
                Expr::While(ref mut wl) => self.parse_while_loop(wl, block, ast, reference),
                Expr::For(fl) => self.parse_for_loop(&mut fl.clone(), block, ast, reference),
                Expr::Impl(ref mut implementation) => {
                    self.parse_impl(implementation, block, ast, reference)
                }
                Expr::Enum(ref mut ast_enum) => {
                    self.parse_enum(ast_enum, block, reference, ast);
                }
                _ => continue,
            }
        }
    }

    fn parse_enum(&'a self, ast_enum: &mut Enum, block: &mut Block<'a>, memory: &mut Memory<'a>, ast: &mut Ast) {
        let kind_type = *memory.datatypes.get("u1").unwrap();
        let kind_field = self.context.new_field(None, kind_type, "kind");
        let mut field_index = 1;
        let mut fields = vec![];
        let mut map = HashMap::new();
        for variant in ast_enum.variants.iter_mut() {
            let mut field_value = None;
            if let Some(ref mut dt) = variant.r#type {
                let field_type = self.parse_datatype(dt, memory);
                let field = self.context.new_field(None, field_type, variant.name.as_str());
                field_value = Some(field);
                fields.push(field);
            }
            map.insert(variant.name.clone(), (field_index, field_value));
            field_index += 1;
        }
        let enum_type = self.context.new_union_type(None, format!(".{}", ast_enum.name.clone()), &fields);
        let union_field = self.context.new_field(None, enum_type, ".variants");
        let dt = self.context.new_struct_type(None, ast_enum.name.clone(), &[kind_field, union_field]);
        memory.enum_variants.insert(dt.as_type(), map);
        memory.datatypes.insert(ast_enum.name.clone(), dt.as_type());
    }

    fn parse_impl(
        &'a self,
        implementation: &mut Impl,
        block: &mut Block<'a>,
        ast: &mut Ast,
        memory: &mut Memory<'a>,
    ) {
        self.parse_impl_block(implementation, ast, memory);
    }

    fn parse_impl_block(
        &'a self,
        implementation: &mut Impl,
        ast: &mut Ast,
        memory: &mut Memory<'a>,
    ) {
        let expr = self
            .get_rc_value(&mut implementation.block.expr[0])
            .unwrap();
        for expr in implementation.block.expr.iter_mut() {
            let expr = self.get_rc_value(expr).unwrap();
            match expr {
                Expr::Function(mut function) => {
                    let old = function.name.name.clone();
                    function.name.name = format!(
                        "{}{}{}",
                        implementation.trait_name, implementation.struct_name, function.name.name
                    );
                    self.parse_function(&mut function, memory, ast);
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

    fn get_rc_value<T: Sized + Clone>(&self, rc: &mut Rc<RefCell<T>>) -> Option<T> {
        Rc::make_mut(rc).get_mut().clone().into()
    }

    fn parse_for_loop(
        &'a self,
        fl: &mut ForLoop,
        block: &mut Block<'a>,
        ast: &mut Ast,
        memory: &mut Memory<'a>,
    ) {
        let function = block.get_function();
        let mut value = self.parse_value(&mut fl.range, block, memory, ast);
        let range_type = *memory.datatypes.get("range").unwrap();
        let datatype = match value {
            GccValues::Range(range) => {
                let left_field = range_type.is_struct().unwrap().get_field(0);
                let left = range.access_field(None, left_field);
                left.to_rvalue().get_type()
            }
            GccValues::L(val) => {
                if val.to_rvalue().get_type() != range_type {
                    let impls = memory
                        .impls
                        .get(&val.to_rvalue().get_type())
                        .expect(&format!(
                            "Could not find implementation of iter for {:?}",
                            val
                        ));
                    impls
                        .iter()
                        .find(|(x, _)| x == "peek")
                        .unwrap()
                        .1
                        .get_return_type()
                }else{
                    let field = range_type.is_struct().unwrap().get_field(0);
                    let left = val.access_field(None, field);
                    left.to_rvalue().get_type()
                }
            }
            GccValues::R(val) => val.get_type(),
            _ => todo!(),
        };
        let struct_type = *memory.datatypes.get("range").unwrap();
        let struct_dt = struct_type.is_struct().unwrap();
        if let GccValues::L(_) = value {
            if value.rvalue().get_type() == struct_type {
                value = GccValues::Range(value.rvalue());
            }
        }
        match value {
            GccValues::R(_) | GccValues::Range(_) => {
                let (start, end) = match value {
                    GccValues::Range(range) => {
                        let left_field = struct_dt.get_field(0);
                        let right_field = struct_dt.get_field(1);
                        let left = range.access_field(None, left_field);
                        let right = range.access_field(None, right_field);
                        (left, right)
                    }
                    _ => unreachable!("{:?}", fl.range),
                };
                let pivot = function.new_local(None, datatype, fl.pivot.clone());
                memory
                    .variables
                    .get_mut(&memory.function_scope)
                    .unwrap()
                    .insert(fl.pivot.clone(), pivot);
                block.add_assignment(None, pivot, start);
                let condition =
                    self.context
                        .new_comparison(None, ComparisonOp::Equals, pivot, end);
                let mut loop_block = function.new_block(self.uuid());
                memory.blocks.insert(loop_block, false);
                let index = function.new_local(None, start.to_rvalue().get_type(), self.uuid());
                block.add_assignment(None, index, start.to_rvalue());
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
                self.parse_block(&mut fl.block, &mut loop_block, memory, ast);
                memory.blocks.insert(loop_block, true);
                loop_block.end_with_jump(None, condition_block);
                *block = continue_block;
            }
            GccValues::L(value) => {
                let struct_type = *memory.datatypes.get("range").unwrap();
                if value.to_rvalue().get_type() != struct_type {
                    let impls = memory.impls.get(&value.to_rvalue().get_type()).unwrap();
                    let peek = impls.iter().find(|(x, _)| x == "peek").unwrap();
                    let end = impls.iter().find(|(x, _)| x == "ended").unwrap();
                    let start = self
                        .context
                        .new_call(None, peek.1, &[value.get_address(None)]);
                    let end = self
                        .context
                        .new_call(None, end.1, &[value.get_address(None)]);
                    let dt = *memory.datatypes.get("bool").unwrap();
                    let mut condition = self.context.new_comparison(
                        None,
                        ComparisonOp::Equals,
                        end,
                        self.context.new_rvalue_from_int(dt, 1),
                    );
                    if !condition.get_type().is_compatible_with(dt) {
                        condition = self.context.new_cast(None, condition, dt);
                    }
                    let mut loop_block = function.new_block(self.uuid());
                    memory.blocks.insert(loop_block, false);
                    let pivot = function.new_local(None, start.get_type(), self.uuid());
                    block.add_assignment(None, pivot, start);
                    memory
                        .variables
                        .get_mut(&memory.function_scope)
                        .unwrap()
                        .insert(fl.pivot.clone(), pivot);
                    let continue_block = function.new_block(self.uuid());
                    let condition_block = function.new_block(self.uuid());
                    condition_block.end_with_conditional(None, condition, continue_block, loop_block);
                    let next = impls.iter().find(|(x, _)| x == "next").unwrap();
                    let next = self
                        .context
                        .new_call(None, next.1, &[value.get_address(None)]);
                    loop_block.add_assignment(None, pivot, next);
                    memory.blocks.insert(condition_block, true);
                    block.end_with_jump(None, condition_block);
                    self.parse_block(&mut fl.block, &mut loop_block, memory, ast);
                    memory.blocks.insert(loop_block, true);
                    loop_block.end_with_jump(None, condition_block);
                    *block = continue_block
                }
            }
            x => panic!("Found {:?}", x),
        }
        memory.blocks.insert(*block, true);
    }

    fn parse_while_loop(
        &'a self,
        wl: &mut WhileLoop,
        block: &mut Block<'a>,
        ast: &mut Ast,
        memory: &mut Memory<'a>,
    ) {
        let active_function = block.get_function();
        let mut while_loop = active_function.new_block(self.uuid());
        let condition_block = active_function.new_block(self.uuid());
        block.end_with_jump(None, condition_block);
        let continue_block = active_function.new_block(self.uuid());
        *block = continue_block;
        let aux = while_loop;
        let rtn = self.parse_block(
            Rc::make_mut(&mut wl.block).get_mut(),
            &mut while_loop,
            memory,
            ast,
        );
        let condition = self.parse_value(&mut wl.condition, block, memory, ast);
        while_loop.end_with_jump(None, condition_block);
        condition_block.end_with_conditional(None, condition.rvalue(), aux, continue_block);
        if rtn != GccValues::Nil {
            panic!("Can't return inside of while loop. If you want to break early, use if.")
        }
    }

    fn add_link(&'a self, lib_link: &LibLink) {
        let (_, path) = std::env::vars().find(|(x, _)| x == "APOLLO_ROOT").unwrap();
        if lib_link.lib_name.ends_with(".o") || lib_link.lib_name.ends_with(".a") {
            self.context
                .add_driver_option(format!("-L{} -l:{}", path, lib_link.lib_name));
        } else {
            self.context.add_driver_option(format!(
                "-l{}",
                lib_link.lib_name.split(".").peekable().peek().unwrap(),
            ))
        }
    }

    fn setup_entry_point(
        &'a self,
        imports: &mut HashSet<String>,
        ast: &mut Ast,
        memory: &mut Memory<'a>,
    ) -> Block<'a> {
        self.gen_primitive_types(memory);
        self.gen_units(memory);
        self.add_builtin_functions(memory);
        self.build_imports(imports, memory, ast);
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

    fn compile_program(&'a self, is_debug: bool) {
        self.context.add_driver_option("-march=x86-64-v4");
        self.context.dump_to_file("apollo.c", false);
        if is_debug {
        } else {
            self.context
                .set_optimization_level(gccjit::OptimizationLevel::Aggressive);
        }
        self.context.set_program_name("apollo");
        self.context
            .compile_to_file(gccjit::OutputKind::Executable, "apollo");
        self.context
            .compile_to_file(gccjit::OutputKind::DynamicLibrary, "apollo.so");
        self.context
            .compile_to_file(gccjit::OutputKind::Assembler, "apollo.s");
    }

    pub fn gen_bytecode(
        &'a self,
        ast: &mut Ast,
        imports: &mut HashSet<String>,
        memory: &mut Memory<'a>,
        should_compile: bool,
        is_debug: bool,
    ) {
        let mut block = self.setup_entry_point(imports, ast, memory);
        self.parse_expression(ast, memory, &mut block);
        block.end_with_return(
            None,
            self.context
                .new_rvalue_from_int(<i32 as Typeable>::get_type(&self.context), 0),
        );
        if should_compile {
            self.compile_program(is_debug);
        }
    }

    fn parse_trait(
        &'a self,
        r#trait: &mut structs::Trait,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
    ) {
        let mut fields = Vec::new();
        let mut struct_fields = Vec::new();
        let mut counter = 0;
        let mut new_struct = HashMap::new();
        for field in r#trait.fields.iter_mut() {
            new_struct.insert(field.name.clone(), counter);
            counter += 1;
            let field_type = self.parse_datatype(&mut field.datatype.clone(), memory);
            let struct_field = self.context.new_field(None, field_type, &field.name);
            struct_fields.push(struct_field);
            fields.push((field.name.clone(), field_type));
            memory.field_types.insert(struct_field, field_type);
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

    fn parse_struct(&'a self, r#struct: &mut StructDecl, memory: &mut Memory<'a>) {
        if r#struct.name[0..1] != r#struct.name.to_uppercase()[0..1] {
            panic!(
                "Struct name must begin with uppercase letter. Working on struct {}",
                r#struct.name
            );
        }
        let mut fields = Vec::new();
        let mut counter = 0;
        let mut new_struct = HashMap::new();
        for r#trait in r#struct.traits.iter() {
            let trait_fields = memory.traits.get(r#trait).unwrap();
            for (field, datatype) in trait_fields.iter() {
                new_struct.insert(field.clone(), counter);
                let field = self.context.new_field(None, *datatype, field);
                fields.push(field);
                memory.field_types.insert(field, *datatype);
                counter += 1;
            }
        }
        for field in r#struct.fields.iter_mut() {
            new_struct.insert(field.name.clone(), counter);
            counter += 1;
            let field = self.parse_field(field, memory);
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

    fn build_imports(
        &'a self,
        all_imports: &mut HashSet<String>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) {
        let imports = &mut ast.imports;
        for (import, ref mut ast) in imports.iter_mut() {
            println!("{:?}", import);
            if all_imports.contains(import.name.as_str()) {
                continue;
            }
            all_imports.insert(import.name.clone());
            let imported_ast = Rc::get_mut(ast).unwrap();
            self.gen_bytecode(imported_ast.get_mut(), all_imports, memory, false, false);
            //self.push_to_module(&import, memory, &mut new_memory);
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
                    .insert(format!("{}::{}", base_name, name), fields.clone());
            });
            new_memory.trait_types.iter().for_each(|(types, name)| {
                memory
                    .trait_types
                    .insert(*types, format!("{}::{}", base_name, name));
            });
            new_memory.datatypes.iter().for_each(|(name, datatype)| {
                memory
                    .datatypes
                    .insert(format!("{}::{}", base_name, name), *datatype);
            });
            new_memory.field_types.iter().for_each(|(field, datatype)| {
                memory.field_types.insert(*field, *datatype);
            });
            new_memory
                .function_addresses
                .iter()
                .for_each(|(name, address)| {
                    memory
                        .function_addresses
                        .insert(format!("{}::{}", base_name, name), *address);
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
        overloaded: &mut Overloaded,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) {
        let lhs = match overloaded.lhs {
            structs::OverloadedLHS::FieldAccess(ref mut access) => {
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
        let mut rhs = self.parse_value(&mut overloaded.rhs, block, memory, ast);
        if !lhs
            .rvalue()
            .get_type()
            .is_compatible_with(rhs.rvalue().get_type())
        {
            rhs = GccValues::R(self.new_cast(lhs.rvalue().get_type(), &rhs, memory));
        }
        block.add_assignment_op(None, lhs.dereference(), op, rhs.rvalue());
    }

    fn parse_assignment(
        &'a self,
        assignment: &mut structs::Assignment,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) {
        match assignment.var {
            AssignVar::Access(ref mut access) => {
                let var = self
                    .parse_array_access(access, block, memory, ast)
                    .dereference();
                let value = self.parse_value(&mut assignment.value, block, memory, ast);
                let value = self.new_cast(var.to_rvalue().get_type(), &value, memory);
                block.add_assignment(None, var, value.to_rvalue());
            }
            AssignVar::Name(ref name) => {
                let var = self.parse_name(name, memory, block).dereference();
                let value = self.parse_value(&mut assignment.value, block, memory, ast);
                let value = self.new_cast(var.to_rvalue().get_type(), &value, memory);
                block.add_assignment(None, var, value);
            }
            AssignVar::FieldAccess(ref mut access) => {
                let var = self
                    .parse_field_access(access, None, block, memory, ast)
                    .dereference();
                let value = self.parse_value(&mut assignment.value, block, memory, ast);
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
        rtn: &mut structs::Return,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) {
        if let Some(ref mut value) = rtn.value {
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
        value: &mut structs::Value,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) -> GccValues<'a> {
        let rtn = match value.value {
            ValueEnum::Int(number) => self.parse_int(number),
            ValueEnum::UInt(number) => self.parse_uint(number),
            ValueEnum::Float(number) => self.parse_float(number),
            ValueEnum::String(ref string) => self.parse_string(string),
            ValueEnum::Name(ref name) => self.parse_name(name, memory, block),
            ValueEnum::Bool(boolean) => self.parse_bool(boolean, memory),
            ValueEnum::Call(ref mut call) => self.parse_call(call, None, block, memory, ast),
            ValueEnum::Array(ref mut array) => self.parse_array(array, block, memory, ast),
            ValueEnum::ArrayAccess(ref mut access) => {
                let mut access = self.get_rc_value(access).unwrap();
                let lvalue = self.parse_array_access(&mut access, block, memory, ast);
                lvalue
            }
            ValueEnum::Char(ref r#char) => self.parse_char(char, memory),
            ValueEnum::Constructor(ref mut constructor) => {
                let mut constructor = self.get_rc_value(constructor).unwrap();
                self.parse_constructor(&mut constructor, block, memory, ast)
            }
            ValueEnum::FieldAccess(ref mut access) => {
                let mut access = self.get_rc_value(access).unwrap();
                self.parse_field_access(&mut access, None, block, memory, ast)
            }
            ValueEnum::Casting((ref mut value, ref mut target)) => {
                let mut value = self.get_rc_value(value).unwrap();
                let value = self.parse_value(&mut value, block, memory, ast);
                let target = self.parse_datatype(target, memory);
                GccValues::R(self.new_cast(target, &value, memory))
            }
            ValueEnum::Range(ref mut range) => self.parse_range(range, block, memory, ast),
            ValueEnum::BinaryOp(ref mut binary_op) => {
                let mut binary_op = self.get_rc_value(binary_op).unwrap();
                self.parse_binary_op(&mut binary_op, block, memory, ast)
            }
            ValueEnum::UnaryOp(ref mut unary_operation) => {
                let mut unary_op = self.get_rc_value(unary_operation).unwrap();
                self.parse_unary_op(&mut unary_op, block, memory, ast)
            }
            ValueEnum::Enum(ref mut enum_value) => {
                self.parse_enum_value(enum_value, block, memory, ast)
            }
            ref val => unreachable!("Found value enum {:?} while parsing value", val),
        };
        rtn
    }

    fn parse_enum_value(&'a self, enum_value: &mut Rc<RefCell<EnumValue>>, block: &mut Block<'a>, memory: &mut Memory<'a>, ast: &mut Ast) -> GccValues<'_> {
        let mut enum_value = self.get_rc_value(enum_value).unwrap();
        let datatype = memory.datatypes.get(&enum_value.datatype).unwrap().clone();
        let kind_field = datatype.is_struct().unwrap().get_field(0);
        let variant_field = datatype.is_struct().unwrap().get_field(1);
        let variants = memory.enum_variants.get(&datatype).unwrap().clone();
        println!("{:?}", enum_value);
        let (index, active_field) = variants.get(&enum_value.variant).unwrap();
        let function = block.get_function();
        let dummy = function.new_local(None, datatype, ".");
        let active_variant = dummy.access_field(None, kind_field);
        block.add_assignment(None, active_variant, self.context.new_rvalue_from_int(*memory.datatypes.get("u1").unwrap(), *index));
        if let Some(ref mut inner) = enum_value.inner {
            let value = self.parse_value(inner, block, memory, ast);
            let variant_field = dummy.access_field(None, variant_field);
            let active = variant_field.access_field(None, active_field.unwrap());
            block.add_assignment(None, active, value.rvalue());
        }
        GccValues::R(dummy.to_rvalue())
    }

    fn parse_range(
        &'a self,
        range: &mut RangeValue,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) -> GccValues<'a> {
        match range {
            RangeValue::Iterable(ref mut value) => {
                self.parse_value(&mut self.get_rc_value(value).unwrap(), block, memory, ast)
            }
            RangeValue::Range(ref mut range) => {
                let mut range = self.get_rc_value(range).unwrap();
                let start = self.parse_value(&mut range.start, block, memory, ast);
                let end = self.parse_value(&mut range.end, block, memory, ast);
                let struct_type = *memory.datatypes.get("range").unwrap();
                let struct_dt = struct_type.is_struct().unwrap();
                let start_field = struct_dt.get_field(0);
                let end_field = struct_dt.get_field(1);
                match range.range_type {
                    RangeType::Exclusive => {
                        let range = self.context.new_struct_constructor(None, struct_type, Some(&[start_field, end_field]), &[start.rvalue(), end.rvalue()]);
                        GccValues::Range(range)
                    }
                    RangeType::Inclusive => {
                        let end = self.context.new_binary_op(
                            None,
                            BinaryOp::Plus,
                            end.rvalue().get_type(),
                            end.rvalue(),
                            self.context.new_rvalue_from_int(end.rvalue().get_type(), 1),
                        );
                        let range = self.context.new_struct_constructor(None, struct_type, Some(&[start_field, end_field]), &[start.rvalue(), end]);
                        GccValues::Range(range)
                    }
                }
            }
        }
    }

    fn parse_field_access(
        &'a self,
        access: &mut structs::FieldAccess,
        aux: Option<GccValues<'a>>,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) -> GccValues<'a> {
        let value = self.parse_field_access_name(&mut access.name, aux, block, memory, ast);
        let mut next = self.get_rc_value(&mut access.next).unwrap();
        if let Some(ref mut next) = next {
            return self.parse_field_access(next, Some(value), block, memory, ast);
        }
        value
    }

    fn parse_field_access_name(
        &'a self,
        name: &mut FieldAccessName,
        aux: Option<GccValues<'a>>,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) -> GccValues<'a> {
        match name {
            FieldAccessName::Name(ref name) => match aux {
                Some(val) => {
                    let mut value = if let Some(field) = val.rvalue().get_type().is_struct() {
                        let struct_fields = memory.structs.get(&field).unwrap();
                        let field_index = struct_fields.get(&name.name).expect(&format!(
                            "Field {} does not exist on struct {:?}",
                            name.name, field
                        ));
                        let field = field.get_field(*field_index);
                        GccValues::L(val.dereference().access_field(None, field))
                    } else if let Some(field) = val.dereference().to_rvalue().get_type().is_struct()
                    {
                        let struct_fields = memory.structs.get(&field).unwrap();
                        let field_index = struct_fields
                            .get(&name.name)
                            .expect(&format!("Struct field {} is undefined", name.name));
                        let field = field.get_field(*field_index);
                        GccValues::L(val.dereference().access_field(None, field))
                    } else {
                        panic!(
                            "Tried to access {}, but {:?} is not a struct. It is {:?}",
                            name.name,
                            val,
                            val.dereference().to_rvalue().get_type()
                        )
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
            FieldAccessName::Call(ref mut call) => match aux {
                Some(val) => self.parse_call(call, Some(val), block, memory, ast),
                None => self.parse_call(call, None, block, memory, ast),
            },
            FieldAccessName::ArrayAccess(ref mut access) => match aux {
                Some(val) => {
                    if let ValueEnum::Name(ref name) = access.value.value {
                        let lvalue = self.parse_field_access_name(
                            &mut FieldAccessName::Name(name.clone()),
                            Some(val),
                            block,
                            memory,
                            ast,
                        );
                        let index = self.parse_value(&mut access.index, block, memory, ast);
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
        constructor: &mut Constructor,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) -> GccValues<'a> {
        //let decl = self.ast_context.structs.get(&constructor.name).unwrap();
        let mut values = Vec::new();
        let struct_type = memory
            .datatypes
            .get(&constructor.name)
            .expect(&format!("Struct {} was not found", constructor.name));
        let struct_type = struct_type
            .is_struct()
            .expect(&format!("{} is not a struct", constructor.name));
        let fields = memory
            .structs
            .get(&struct_type)
            .expect(&format!("Struct {} was not found", constructor.name))
            .clone();
        for field in constructor.fields.iter_mut() {
            let value = self
                .parse_value(&mut field.value, block, memory, ast)
                .rvalue();
            let name = field.name.clone();
            let field = fields.get(&field.name).expect(&format!(
                "Struct {} does not contain field {} of type {:?}",
                constructor.name,
                field.name,
                value.get_type()
            ));

            let target_type = memory
                .field_types
                .get(&struct_type.get_field(*field))
                .expect(&format!("Couldn't find field {}", name));
            let value = self.new_cast(*target_type, &GccValues::R(value), memory);
            values.push(value);
        }
        GccValues::R(self.context.new_struct_constructor(
            None,
            struct_type.as_type(),
            None,
            values.as_slice(),
        ))
    }

    fn parse_field(
        &'a self,
        field: &mut structs::FieldDecl,
        memory: &mut Memory<'a>,
    ) -> gccjit::Field<'a> {
        let datatype = self.parse_datatype(&mut field.datatype, memory);
        let field = self.context.new_field(None, datatype, field.name.clone());
        memory.field_types.insert(field, datatype);
        field
    }

    fn parse_char(&'a self, c: &char, memory: &mut Memory<'a>) -> GccValues<'a> {
        GccValues::R(self.context.new_rvalue_from_int(
            *memory.datatypes.get("char").unwrap(),
            *c.to_string().bytes().peekable().peek().unwrap() as i32,
        ))
    }

    fn parse_array_access(
        &'a self,
        access: &mut structs::ArrayAccess,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) -> GccValues<'a> {
        let rvalue = self
            .parse_value(&mut access.value, block, memory, ast)
            .rvalue();
        let index = self
            .parse_value(&mut access.index, block, memory, ast)
            .rvalue();
        GccValues::L(self.context.new_array_access(None, rvalue, index))
    }

    fn parse_array(
        &'a self,
        array: &mut structs::Array,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) -> GccValues<'a> {
        let array_type = self.parse_datatype(&mut array.datatype, memory);

        let elements = array
            .elements
            .iter_mut()
            .map(|x| self.parse_value(x, block, memory, ast).rvalue())
            .collect::<Vec<RValue<'a>>>();
        let array = self
            .context
            .new_array_constructor(None, array_type, &elements);
        GccValues::R(array)
    }

    fn parse_block(
        &'a self,
        ast_block: &mut structs::Block,
        new_block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) -> GccValues<'a> {
        self.parse_expression(&mut ast_block.to_ast(), memory, new_block);
        if let Some(ref mut rtn) = ast_block.box_return {
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
        function: &mut structs::Function,
        memory: &mut Memory<'a>,
    ) -> Vec<Parameter<'a>> {
        let mut arg_map = HashMap::new();
        let params = self.parse_args(&mut function.args, memory);
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

    fn parse_function(
        &'a self,
        function: &mut structs::Function,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) {
        if memory.functions.contains_key(&function.name.name) {
            return;
        }
        let return_type = match function.return_type {
            Some(ref mut data_type) => self.parse_datatype(data_type, memory),
            None => <() as Typeable>::get_type(self.context),
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

        match function.kind {
            FunctionKind::Native | FunctionKind::Exported => {
                let aux = memory.function_scope.clone();
                memory.function_scope = function.name.name.clone();
                let mut new_block =
                    new_function.new_block(&format!("{}_block", function.name.name));
                let mut block = self.get_rc_value(&mut function.block).unwrap();
                self.parse_block(&mut block, &mut new_block, memory, ast);
                memory.function_scope = aux;
            }
            _ => (),
        };
    }

    fn parse_args(
        &'a self,
        args: &mut Vec<structs::Arg>,
        memory: &mut Memory<'a>,
    ) -> Vec<Parameter> {
        let mut params = Vec::new();
        for arg in args {
            let datatype = self.parse_datatype(&mut arg.datatype, memory);
            let param = self.context.new_parameter(None, datatype, &arg.name.name);
            params.push(param);
        }
        params
    }

    fn parse_datatype(&'a self, datatype: &mut structs::Type, memory: &mut Memory<'a>) -> Type<'_> {
        let r#type = match datatype.datatype {
            DataType::Bool => <bool as Typeable>::get_type(self.context),
            DataType::Int(bytecount) => *memory.datatypes.get(&format!("i{}", bytecount)).unwrap(),
            DataType::UInt(bytecount) => *memory.datatypes.get(&format!("u{}", bytecount)).unwrap(),
            DataType::Array(ref mut array_type) => {
                let mut array_type = self.get_rc_value(array_type).unwrap();
                match array_type.size.value {
                    ValueEnum::Int(size) => {
                        let format =
                            format!("array{}{}", array_type.data_type.datatype.to_string(), size);
                        if let Some(array_type) = memory.datatypes.get(&format) {
                            *array_type
                        } else {
                            let element_type =
                                self.parse_datatype(&mut array_type.data_type, memory);
                            let dt = self.context.new_array_type(None, element_type, size as u64);
                            memory.datatypes.insert(format, dt);
                            dt
                        }
                    }
                    _ => {
                        panic!("{:?}", array_type);
                    }
                }
            }
            DataType::String => *memory.datatypes.get("string").unwrap(),
            DataType::Char => *memory.datatypes.get("char").unwrap(),
            DataType::StructType(ref name) => {
                *if let Some(val) = memory.datatypes.get(name) {
                    val
                } else {
                    panic!("{:?} is undefined", datatype)
                }
            }
            DataType::Float(bytecount) => {
                *memory.datatypes.get(&format!("f{}", bytecount)).unwrap()
            }
            DataType::Trait(ref name) => *memory.datatypes.get(name).unwrap(),
            DataType::Any => *memory.datatypes.get("Any").unwrap(),
            _ => unreachable!(),
        };
        if datatype.is_ref {
            let mut dt = r#type.make_pointer();
            for _ in 0..datatype.ref_count - 1 {
                dt = r#type.make_pointer();
            }
            memory.pointer_types.insert(dt);
            dt
        } else {
            r#type
        }
    }

    fn parse_if(
        &'a self,
        ast_if: &mut structs::If,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) -> Block<'_> {
        let mut tb_declared = None;
        let mut condition = if let Some(ref mut ast_condition) = ast_if.condition {
            let mut condition = self.get_rc_value(ast_condition).unwrap();
            let mut condition = self
                .parse_value(&mut condition, block, memory, ast)
                .rvalue();
            if ast_if.not {
                condition = self.context.new_unary_op(
                    None,
                    UnaryOp::LogicalNegate,
                    condition.get_type(),
                    condition,
                );
            }
            condition
        }else{
            let enum_match = ast_if.enum_match.as_ref().unwrap();
            let vars = memory.variables.get(&memory.function_scope).unwrap();
            let var = vars.get(&enum_match.name).unwrap();
            let enum_type = var.to_rvalue().get_type().is_struct().unwrap();
            let variants = memory.enum_variants.get(&enum_type.as_type()).unwrap();
            let (index, _field) = variants.get(&enum_match.variant).unwrap();
            let kind_field = enum_type.get_field(0);
            let variant_field = enum_type.get_field(1);
            let active_field = var.access_field(None, kind_field);
            let matching = self.context.new_rvalue_from_int(active_field.to_rvalue().get_type(), *index);
            tb_declared = Some((enum_match.var.clone(), var.access_field(None, variant_field)));
            self.context.new_comparison(None, ComparisonOp::Equals, active_field, matching)
        };
        let function = block.get_function();
        let mut then_block = function.new_block(self.uuid());
        let mut ast_block = self.get_rc_value(&mut ast_if.block).unwrap();
        if let Some((ref name, value)) = tb_declared {
            let local = function.new_local(None, value.to_rvalue().get_type(), name);
            let vars = memory.variables.get_mut(&memory.function_scope).unwrap();
            vars.insert(name.clone(), local);
            then_block.add_assignment(None, local, value.to_rvalue());
        }
        self.parse_block(&mut ast_block, &mut then_block, memory, ast);
        let mut else_should_continue = false;
        let mut else_block = function.new_block(self.uuid());
        block.end_with_conditional(None, condition, then_block, else_block);
        if let Some(ref mut otherwise) = ast_if.otherwise {
            let mut otherwise = self.get_rc_value(otherwise).unwrap();
            match otherwise {
                Otherwise::Block(ref mut block) => {
                    else_should_continue = block.box_return.is_none();
                    self.parse_block(block, &mut else_block, memory, ast);
                }
                Otherwise::If(ref mut ast_if) => {
                    let block = self.get_rc_value(&mut ast_if.block).unwrap();
                    else_should_continue = block.box_return.is_none() && ast_if.otherwise.is_some();
                    else_block = self.parse_if(ast_if, &mut else_block, memory, ast);
                }
            }
        };
        let ast_block = self.get_rc_value(&mut ast_if.block).unwrap();
        let else_block = if else_should_continue {
            let new = function.new_block(self.uuid());
            else_block.end_with_jump(None, new);
            new
        }else{
            else_block
        };
        if ast_block.box_return.is_none() {
            then_block.end_with_jump(None, else_block);
        }
        else_block
    }

    fn parse_declaration(
        &'a self,
        declaration: &mut structs::Declaration,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) {
        match declaration.value.as_mut().unwrap().value {
            ValueEnum::Constructor(ref mut constructor) => {
                let constructor = self.get_rc_value(constructor).unwrap();
                let mut map = HashMap::new();
                map.insert(declaration.name.name.clone(), constructor.name.clone());
                memory
                    .constructors
                    .insert(memory.function_scope.clone(), map);
            }
            ValueEnum::Call(ref call) => {
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
        let value = if let Some(ref mut value) = declaration.value {
            Some(self.parse_value(value, block, memory, ast))
        } else {
            None
        };
        let function = block.get_function();
        if let Some(ref mut dt) = declaration.datatype {
            let data_type = self.parse_datatype(dt, memory);
            let lvalue = function.new_local(None, data_type, &declaration.name.name);
            if value.is_some() {
                let value = self.new_cast(data_type, &value.unwrap(), memory);
                block.add_assignment(None, lvalue, value);
            }
            let variables = memory.variables.get_mut(&memory.function_scope).unwrap();
            variables.insert(declaration.name.name.clone(), lvalue);
        } else {
            let dt = value.as_ref().unwrap().rvalue().get_type();
            let lvalue = function.new_local(None, dt, &declaration.name.name);
            let value = value.as_ref().unwrap().rvalue();
            block.add_assignment(None, lvalue, value);
            let variables = memory.variables.get_mut(&memory.function_scope).unwrap();
            variables.insert(declaration.name.name.clone(), lvalue);
        }
    }

    fn parse_params(
        &'a self,
        args: &mut Vec<structs::Value>,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) -> Vec<GccValues<'_>> {
        let mut params = Vec::new();
        for value in args {
            params.push(self.parse_value(value, block, memory, ast));
        }
        params
    }

    fn size_of(&'a self, value: &GccValues<'a>, memory: &mut Memory<'a>) -> i32 {
        let dt = value.rvalue().get_type();
        let alignment = value.dereference().get_alignment();
        let size = if let Some(struct_type) = dt.is_struct() {
            let mut total_size = 0;
            for i in 0..struct_type.get_field_count() {
                let field = struct_type.get_field(i as i32);
                let field = value.dereference().access_field(None, field);
                total_size += self.size_of(&GccValues::L(field), memory);
            }
            total_size + alignment
        } else {
            if memory.pointer_types.get(&dt).is_some() {
                8
            } else {
                dt.get_size() as i32
            }
        };
        size + alignment
    }

    fn parse_call(
        &'a self,
        call: &mut structs::Call,
        field: Option<GccValues<'a>>,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) -> GccValues<'a> {
        let mut args = self.parse_params(&mut call.args, block, memory, ast);
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
                .new_rvalue_from_int(*memory.datatypes.get("bool").unwrap(), value);
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
                .new_rvalue_from_int(*memory.datatypes.get("i4").unwrap(), value as i32);
            return GccValues::R(rvalue);
        }
        if call.name.name == "size_of" {
            return GccValues::R(self.context.new_rvalue_from_int(
                *memory.datatypes.get("i4").unwrap(),
                self.size_of(&args[0], memory),
            ));
        }
        if !memory.functions.contains_key(&call.name.name) {
            let mut function = ast
                .context
                .functions
                .get_mut(&call.name.name)
                .expect("Couldn't find function")
                .clone();
            self.parse_function(&mut function, memory, ast);
        }
        let function = memory.functions.get(&call.name.name).unwrap().clone();
        if let Some(field) = field {
            let dt = function.get_param(0).to_rvalue().get_type();
            let mut vec = Vec::new();
            if dt.is_compatible_with(*memory.datatypes.get("Any").unwrap()) {
                vec.push(field);
            } else if dt.is_compatible_with(field.rvalue().get_type()) {
                vec.push(GccValues::R(field.rvalue()));
            } else {
                vec.push(GccValues::R(field.get_reference()));
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
        let value = self.context.new_call(None, function, &params);
        if call.neg {
            GccValues::R(self.context.new_unary_op(
                None,
                UnaryOp::LogicalNegate,
                value.get_type(),
                value,
            ))
        } else {
            GccValues::R(value)
        }
    }

    fn new_cast(
        &'a self,
        left_type: Type<'a>,
        right: &GccValues<'a>,
        memory: &mut Memory<'a>,
    ) -> RValue<'a> {
        let mut rtn = right.rvalue();
        let name = memory.trait_types.get_mut(&left_type);
        if left_type.is_compatible_with(rtn.get_type()) {
            return rtn;
        }
        if name.is_some() {
            let name = name.unwrap().clone();
            rtn = self.struct_to_trait(right.rvalue(), &name, left_type, memory);
        } else if !left_type.is_compatible_with(rtn.get_type())
            && left_type.is_compatible_with(*memory.datatypes.get("Any").unwrap())
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
        operation: &mut Rc<RefCell<structs::Operation>>,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) -> GccValues<'a> {
        use structs::Operation;
        match Rc::get_mut(operation).unwrap().get_mut().clone() {
            Operation::BinaryOp(ref mut binary_op) => {
                self.parse_binary_op(binary_op, block, memory, ast)
            }
            Operation::UnaryOp(ref mut unary_op) => {
                self.parse_unary_op(unary_op, block, memory, ast)
            }
        }
    }

    fn parse_binary_op(
        &'a self,
        binary_op: &mut structs::BinaryOp,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
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
        let mut lhs = self.get_rc_value(&mut binary_op.lhs).unwrap();
        let lhs = self.parse_value(&mut lhs, block, memory, ast);
        let mut rhs = self.get_rc_value(&mut binary_op.rhs).unwrap();
        let mut rhs = self.parse_value(&mut rhs, block, memory, ast);
        if !lhs
            .rvalue()
            .get_type()
            .is_compatible_with(rhs.rvalue().get_type())
        {
            rhs = GccValues::R(self.new_cast(lhs.rvalue().get_type(), &mut rhs, memory));
        }
        GccValues::R(match op {
            Helper::Binary(binary_op) => lhs.binary_op(rhs, binary_op, &self.context).rvalue(),
            Helper::Comp(comparison_op) => lhs
                .comparison_op(rhs, comparison_op, &self.context)
                .rvalue(),
        })
    }

    fn parse_unary_op(
        &'a self,
        unary_op: &mut structs::UnaryOp,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) -> GccValues<'_> {
        use structs::Operations;
        let mut value = self.get_rc_value(&mut unary_op.value).unwrap();
        let value = self.parse_value(&mut value, block, memory, ast);
        let op = match unary_op.prefix {
            Operations::Neg => Some(UnaryOp::Minus),
            Operations::Not => Some(UnaryOp::LogicalNegate),
            _ => None,
        };
        if let Some(op) = op {
            let data_type = value.rvalue().get_type();
            GccValues::R(
                self.context
                    .new_unary_op(None, op, data_type, value.rvalue()),
            )
        } else {
            value
        }
    }

    fn parse_bool(&self, boolean: bool, memory: &mut Memory<'a>) -> GccValues<'_> {
        let data_type = *memory.datatypes.get("bool").unwrap();
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
                .expect(&format!("Datatype {} does not exist", name.name));
            return GccValues::Type(*datatype);
        }
        let value = if let Some(var) = variables.get(&name.name) {
            self.access_name(var, name)
        } else if let Some(address) = memory.function_addresses.get(&name.name) {
            GccValues::R(*address)
        } else {
            panic!(
                "Variable {} not found. Working on {:?} inside {:?}",
                name.name, name, block
            )
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
