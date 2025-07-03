use gccjit::{
    BinaryOp, Block, ComparisonOp, Context, LValue, Parameter, RValue, ToLValue, ToRValue, Type,
    Typeable, UnaryOp,
};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use super::memory::Memory;
use super::parser::Ast;
use super::structs::{
    self, AssignVar, Constructor, DataType, Enum, EnumValue, FieldAccessName, ForLoop, Impl, ImplMethod, Name, Overloaded, OverloadedOp, ParameterType, RangeValue, RefOp, StructDecl, Value, ValueEnum
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
    functions_to_build: HashMap<String, structs::Function>
}

impl<'a> GccContext<'a> {
    pub fn new(context: &'a Context<'a>) -> Self {
        let imports = HashSet::new();
        Self { imports, context, functions_to_build: HashMap::new() }
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
        memory.datatypes.insert("ui1".into(), uint_1);
        memory.datatypes.insert("ui2".into(), uint_2);
        memory.datatypes.insert("ui4".into(), uint_4);
        memory.datatypes.insert("ui8".into(), uint_8);
        memory.datatypes.insert("ui16".into(), uint_16);
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
        memory.datatypes.insert("#range".into(), range.as_type());
        let data_type = memory.datatypes.get("string").unwrap().clone();
        let len_type = memory.datatypes.get("ui8").unwrap().clone();
        let data_field = self.context.new_field(None, data_type, "data");
        let len_field = self.context.new_field(None, len_type, "len");
        let string = self.context.new_struct_type(None, "String", &[data_field, len_field]);
        memory.datatypes.insert("String".into(), string.as_type());
        let mut string_fields = HashMap::new();
        string_fields.insert("data".into(), 0);
        string_fields.insert("len".into(), 1);
        memory.structs.insert(string, string_fields);
        memory.field_types.insert(data_field, data_type);
        memory.field_types.insert(len_field, len_type);
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
                Expr::Assembly(ref asm) => self.parse_asm(asm, block, reference, ast),
                Expr::VariadicBlock(ref mut ast_block) => {
                    let function = block.get_function();
                    let args = memory.variadic_args.get(&function).unwrap();
                    let offset = function.get_param_count() - args.len();
                    for i in offset..=args.len() {
                        let variables = memory.variables.get_mut(&memory.function_scope).unwrap();
                        let arg = function.get_param(i as i32).to_rvalue();
                        let local = function.new_local(None, arg.get_type(), format!("vararg_{i}"));
                        block.add_assignment(None, local, arg);
                        variables.insert("vararg".into(), local);
                        self.parse_block(ast_block, block, memory, ast);
                    }
                }
                _ => continue,
            }
        }
    }

    fn parse_asm(&'a self, asm: &structs::Assembly, block: &mut Block<'a>, memory: &mut Memory<'a>, ast: &mut Ast) {
        let extended = block.add_extended_asm(None, &asm.asm);
        for arg in asm.input.iter() {
            let name = if let Some(ref name) = arg.name {
                Some(name.as_str())
            }else{
                None
            };
            extended.add_input_operand(name, &arg.constraint, self.parse_value(&mut Value::non_heap(arg.value.clone()), block, memory, ast).rvalue());

        }
        for arg in asm.output.iter() {
               let name = if let Some(ref name) = arg.name {
                Some(name.as_str())
            }else{
                None
            };
            extended.add_output_operand(name, &arg.constraint, self.parse_value(&mut Value::non_heap(arg.value.clone()), block, memory, ast).dereference());
        }
        for clob in asm.clobbered.iter() {
            extended.add_clobber(clob.as_str());
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

    fn setup_impl_args(&'a self, name: String, method: &mut ImplMethod, memory: &mut Memory<'a>) -> Vec<Parameter<'a>> {
       let mut arg_map = HashMap::new();
        let params = self.parse_args(&mut method.params, memory);
        for i in 0..method.params.len() {
            let arg = &method.params[i];
            let param = params[i];
            arg_map.insert(arg.name.name.clone(), param);
        }
        let other_map = arg_map
            .iter()
            .map(|x| (x.0.clone(), x.1.to_lvalue()))
            .collect::<_>();
        memory
            .variables
            .insert(name, other_map);
        params
    }

    fn parse_impl_block(
        &'a self,
        implementation: &mut Impl,
        ast: &mut Ast,
        memory: &mut Memory<'a>,
    ) {
        let mut methods = HashMap::new();
        let target_type = memory.datatypes.get(&implementation.target_name).unwrap().clone();
        let restore = memory.datatypes.clone();
        let mut traits = memory.traits.get(&implementation.trait_name).unwrap().clone();
        for (generic, value) in implementation.generics.iter() {
            if !traits.generics.contains(generic) {
                panic!("Unknown generic type {} for trait {}", generic, implementation.trait_name);
            }
            let dt = memory.datatypes.get(value).unwrap();
            memory.datatypes.insert(generic.into(), *dt);
        }
        for method in implementation.methods.iter_mut() {
            let trait_method = traits.methods.iter_mut().find(|x| x.name == method.name).expect(&format!("No method {} was declared for trait {}", method.name, implementation.trait_name));
            let needs_trait = method.params.iter().find(|x| { if let ParameterType::Implements(_) = x.datatype { true } else { false }} ).is_some();
            if needs_trait {
                memory.impl_with_traits.insert(method.name.clone(), (implementation.trait_name.clone(), method.clone()));
                methods.insert(method.name.clone(), *memory.functions.get("main").unwrap());
                continue
            }
            let fmt = format!(".{}:{}", implementation.trait_name, method.name);
            let params = self.setup_impl_args(fmt.clone(), method, memory);
            let copy = memory.function_scope.clone();
            memory.function_scope = fmt;
            let datatype = if let Some(ref mut dt) = trait_method.datatype {
                self.parse_datatype(dt, memory)
            }else {
                <() as Typeable>::get_type(self.context)
            };
            let function = self.context.new_function(None, gccjit::FunctionType::Internal, datatype, &params, &method.name, false);
            let mut new_block = function.new_block(self.uuid());
            self.parse_block(&mut method.body, &mut new_block, memory, ast);
            memory.function_scope = copy;
            methods.insert(method.name.clone(), function);
            let entry = memory.impl_methods.entry(method.name.clone()).or_insert(HashMap::new());
            entry.insert(target_type, function);
        }
        memory.datatypes = restore;
        let entry = memory.impls.entry(target_type).or_insert(HashMap::new());
        entry.insert(implementation.trait_name.clone(), methods);
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
        let range_type = *memory.datatypes.get("#range").unwrap();
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
                    let iter_methods = impls.get("Iterable").unwrap();

                    iter_methods.get("peek").unwrap().get_return_type()
                }else{
                    let field = range_type.is_struct().unwrap().get_field(0);
                    let left = val.access_field(None, field);
                    left.to_rvalue().get_type()
                }
            }
            GccValues::R(val) => val.get_type(),
            _ => todo!(),
        };
        let struct_type = *memory.datatypes.get("#range").unwrap();
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
                let tail_expr = Expr::Overloaded(Overloaded { lhs: structs::OverloadedLHS::Name(Name { op: None, op_count: 0, name: fl.pivot.clone()}), op: OverloadedOp::Add, rhs: Value::non_heap(ValueEnum::Int(1)) });
                memory.block_tail_expr.push_front(tail_expr);
                memory.blocks.insert(condition_block, true);
                block.end_with_jump(None, condition_block);
                self.parse_block(&mut fl.block, &mut loop_block, memory, ast);
                memory.blocks.insert(loop_block, true);
                loop_block.end_with_jump(None, condition_block);
                *block = continue_block;
            }
            GccValues::L(value) => {
                let struct_type = *memory.datatypes.get("#range").unwrap();
                if value.to_rvalue().get_type() != struct_type {
                    let impls = memory.impls.get(&value.to_rvalue().get_type()).unwrap();
                    let methods = impls.get("Iterable").unwrap();
                    let peek = methods.get("peek").unwrap();
                    let end = methods.get("ended").unwrap();
                    let start = self
                        .context
                        .new_call(None, *peek, &[value.get_address(None)]);
                    let end = self
                        .context
                        .new_call(None, *end, &[value.get_address(None)]);
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
                    let next = methods.get("next").unwrap();
                    let next = self
                        .context
                        .new_call(None, *next, &[value.get_address(None)]);
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
        gen_types: bool
    ) -> Block<'a> {
        if gen_types {
            self.gen_primitive_types(memory);
            self.gen_units(memory);
        }
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

    fn compile_program(&'a self, is_debug: bool, out: String) {
        self.context.add_driver_option("-march=x86-64-v4");
        self.context.dump_to_file(format!("{out}.c"), false);
        if is_debug {
        } else {
            self.context
                .set_optimization_level(gccjit::OptimizationLevel::Aggressive);
        }
        self.context.set_program_name(out.clone());
        self.context
            .compile_to_file(gccjit::OutputKind::Executable, out.clone());
        self.context
            .compile_to_file(gccjit::OutputKind::DynamicLibrary, format!("{out}.so"));
        self.context
            .compile_to_file(gccjit::OutputKind::Assembler, format!("{out}.s"));
    }

    pub fn gen_bytecode(
        &'a self,
        ast: &mut Ast,
        imports: &mut HashSet<String>,
        memory: &mut Memory<'a>,
        should_compile: bool,
        is_debug: bool,
        gen_types: bool,
        out: String
    ) {
        let mut block = self.setup_entry_point(imports, ast, memory, gen_types);
        self.parse_expression(ast, memory, &mut block);
        block.end_with_return(
            None,
            self.context
                .new_rvalue_from_int(<i32 as Typeable>::get_type(&self.context), 0),
        );
        if should_compile {
            self.compile_program(is_debug, out);
        }
    }

    fn parse_trait(
        &'a self,
        r#trait: &mut structs::Trait,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
    ) {
        memory.traits.insert(r#trait.name.clone(), r#trait.clone());
    }

    fn parse_struct(&'a self, r#struct: &mut StructDecl, memory: &mut Memory<'a>) {
        let mut fields = Vec::new();
        let mut counter = 0;
        let mut new_struct = HashMap::new();

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
        fn recursive_descent(node: &structs::Namespace, acc: &mut Vec<String>, str_acc: String) {
            for namespace in node.next.iter() {
                let namespace = namespace.as_ref();
                if !namespace.next.is_empty() {
                    recursive_descent(namespace, acc, format!("{str_acc}::{}", namespace.name));
                }else{
                    let name = format!("{}::{}", str_acc, namespace.name.clone());
                    if !acc.contains(&name) {
                        acc.push(name);
                    }
                }
            }
        }
        let imports = &mut ast.imports;
        for ((import_name, import), ref mut ast) in imports.iter_mut() {
            let mut names = vec![];
            recursive_descent(&import.namespace, &mut names, import.namespace.name.clone());
            for name in names {
                println!("Name is {name}");
                if all_imports.contains(import_name) {
                    continue;
                }
                all_imports.insert(import_name.clone());
                let imported_ast = Rc::get_mut(ast).unwrap();
                let mut new_memory = Memory::new(name.clone());
                new_memory.datatypes = memory.datatypes.clone();
                new_memory.structs = memory.structs.clone();
                new_memory.field_types = memory.field_types.clone();
                self.gen_bytecode(imported_ast.get_mut(), all_imports, &mut new_memory, false, false, false, "".into());
                self.push_to_module(&import, memory, &mut new_memory);
            }
        }
    }

    fn push_to_module(
        &'a self,
        import: &structs::Import,
        memory: &mut Memory<'a>,
        new_memory: &mut Memory<'a>,
    ) {
        fn recursive_descent(node: &structs::Namespace, acc: &mut Vec<String>) {
            for namespace in node.next.iter() {
                let namespace = namespace.as_ref();
                if !namespace.next.is_empty() {
                    recursive_descent(namespace, acc);
                }else{
                    let name = format!("{}::{}", node.name, namespace.name.clone());
                    if !acc.contains(&name) {
                        acc.push(name);
                    }
                }
            }
        }
        let mut imports = vec![];
        recursive_descent(&import.namespace, &mut imports);
        println!("Imports vec {:?}", imports);
        new_memory.functions_with_traits.iter().for_each(|(name, function)| {
            memory.functions_with_traits.insert(name.into(), function.clone());
        });
        for ref import in imports {
            let name = import.split("::").last().unwrap();
            if let Some(function) = new_memory.functions.get(name) {
                println!("Import {name}");
                memory.functions.insert(import.into(), *function);
            }
            if let Some(datatype) = new_memory.datatypes.get(name) {
                memory.datatypes.insert(import.into(), *datatype);
                if let Some(ref struct_type) = datatype.is_struct() {
                    let fields = new_memory.structs.get(struct_type).unwrap();
                    memory.structs.insert(*struct_type, fields.clone());
                    for i in 0..struct_type.get_field_count() {
                        let field = struct_type.get_field(i as i32);
                        let field_type = new_memory.field_types.get(&field).unwrap();
                        memory.field_types.insert(field, *field_type);
                    }
                }
                if let Some(_) = new_memory.trait_types.get(datatype) {
                    memory.trait_types.insert(*datatype, import.into());
                }
            }
            if let Some(traits) = new_memory.traits.get(name) {
                memory.traits.insert(import.into(), traits.clone());
            }
            if let Some(function_address) = new_memory.function_addresses.get(name) {
                memory.function_addresses.insert(import.into(), *function_address);
            }
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
            match name.as_str() {
                "printf" => {
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
                }
                _ => {
                    let function = self.context.get_builtin_function(name);
                    memory.functions.insert(name.trim_start_matches("_").to_string(), function);
                }
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
                let struct_type = *memory.datatypes.get("#range").unwrap();
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
                        .expect(&format!("No memory created for function {}", memory.function_scope))
                        .get(&name.name)
                        .expect(&format!("{} is not in scope for {}", name.name, memory.function_scope));
                    let mut value = GccValues::L(*var);
                    if !memory.should_delay_ref_ops {
                        for _ in 0..name.op_count {
                            value = match name.op {
                                Some(RefOp::Reference) => GccValues::R(var.get_address(None)),
                                Some(RefOp::Dereference) => GccValues::R(var.to_rvalue()),
                                None => GccValues::L(var.to_lvalue()),
                            }
                        }
                    }
                    value
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
        println!("{:?}", memory.datatypes);
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
            c.to_string().as_bytes()[0] as i32,
        ))
    }

    fn parse_array_access(
        &'a self,
        access: &mut structs::ArrayAccess,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) -> GccValues<'a> {
        memory.should_delay_ref_ops = true;
        let rvalue = self
            .parse_value(&mut access.value, block, memory, ast);
        memory.should_delay_ref_ops = false;
        let index = self
            .parse_value(&mut access.index, block, memory, ast)
            .rvalue();
        if let ValueEnum::Name(ref name) = access.value.value {
            let access = self.context.new_array_access(None, rvalue.rvalue(), index);
            self.access_name(&access, name)
        }else{
            GccValues::L(self.context.new_array_access(None, rvalue.rvalue(), index))
        }
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
        let mut aux = ast_block.to_ast(ast.namespace.clone(), ast.context.clone());
        self.parse_expression(&mut aux, memory, new_block);
        aux.expressions = memory.block_tail_expr.make_contiguous().to_vec();
        memory.block_tail_expr.clear();
        self.parse_expression(&mut aux, memory, new_block);
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

    fn function_name(&'a self, traits: &Vec<&structs::Arg>, name: &String) -> String {
        if traits.is_empty() {
            name.clone()
        }else{
            let traits = traits.iter().filter(|x| { if let ParameterType::Implements(_) = x.datatype { true } else { false }} ).map(|x| { let ParameterType::Implements(ref t) = x.datatype else { panic!(); }; (x.name.name.clone(), t) });
            let traits = traits.map(|(name, implements)| format!("{name}{}", implements.iter().fold(String::new(), |acc, elem| format!("{acc}{elem}"))));
            format!("{}{}", name, traits.fold(String::new(), |acc, elem| format!("{acc}{elem}")))
        }
    }

    fn parse_function(
        &'a self,
        function: &mut structs::Function,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) {
        let traits : Vec<&structs::Arg> = function.args.iter().filter(|x| { if let ParameterType::Implements(_) = x.datatype { true } else { false }} ).collect();
        if !traits.is_empty() {
            memory.functions_with_traits.insert(function.name.name.clone(), function.clone());
            return;
        }
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
            false
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
    ) -> Vec<Parameter<'a>> {
        let mut params = Vec::new();
        for arg in args.iter_mut().filter(|x| if let ParameterType::Type(_) = x.datatype { true } else { false }) {
            let ParameterType::Type(ref mut dt) = arg.datatype else { panic!() };
            let datatype = self.parse_datatype(dt, memory);
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
        if let Some(ref mut value) = declaration.value {
            match value.value {
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
        }
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

    fn build_impl_params(&'a self, mut args: Vec<GccValues<'a>>, mut params: Vec<structs::Arg>, memory: &mut Memory<'a>, name: String) -> Vec<Parameter<'a>> {
        let len = params.len();
        let mut rtn = vec![];
        for i in 0..len {
            let param = &mut params[i];
            let arg = &mut args[i];

            match param.datatype {
                ParameterType::Type(ref mut dt) => {
                    let dt = self.parse_datatype(dt, memory);
                    if !dt.is_compatible_with(arg.rvalue().get_type()) {
                        panic!("Incompatible types when calling {} on argument {:?}", &name, arg);
                    }
                }
                ParameterType::Implements(ref traits) => {
                    let impls = memory.impls.get(&arg.rvalue().get_type()).unwrap();
                    for t in traits {
                        if !impls.contains_key(t) { panic!("Type {:?} does not implement trait {}", arg.rvalue().get_type(), t); }
                    }
                }
            }
            rtn.push(self.context.new_parameter(None, arg.rvalue().get_type(), &param.name.name));
        }
        rtn
    }

    fn parse_impl_call(&'a self, partial_args: Vec<GccValues<'a>>, call: &mut structs::Call, field: GccValues<'a>, block: &mut Block<'a>, memory: &mut Memory<'a>, ast: &mut Ast) -> GccValues<'a> {
        let mut args = vec![field.clone()];
        args.extend(partial_args);
        let mut fn_name = call.name.name.clone();
        let to_impl = if let Some(to_impl) = memory.impl_with_traits.get(&call.name.name) {
            fn_name = self.function_name(&to_impl.1.params.iter().collect(), &call.name.name);
            Some(to_impl.clone())
        }else{
            None
        };
        let impl_map = memory.impl_methods.get(&fn_name).unwrap().clone();
        let method = impl_map.get(&field.rvalue().get_type());
        if method.is_none() {
            let (_, mut to_impl) = to_impl.unwrap();
            if to_impl.params.len() != args.len() { panic!("Sizes do not match.") }
            let params = self.build_impl_params(args.clone(), to_impl.params.clone(), memory, call.name.name.clone());
            let datatype = if let Some(ref mut dt) = to_impl.datatype {
                self.parse_datatype(dt, memory)
            }else {
                <() as Typeable>::get_type(self.context)
            };
            let function = self.context.new_function(None, gccjit::FunctionType::Internal, datatype, &params, &fn_name, false);
            let entry = memory.impls.entry(field.rvalue().get_type()).or_insert(HashMap::new());
            let (_, map) = entry.iter_mut().find(|(_, value)| value.contains_key(&call.name.name)).unwrap();
            map.insert(fn_name.clone(), function);
            let entry = memory.impl_methods.entry(fn_name.clone()).or_insert(HashMap::new());
            entry.insert(field.rvalue().get_type(), function);

        }

        let method = impl_map.get(&field.rvalue().get_type()).unwrap();

        let value = self.context.new_call(None, *method, &args.iter().map(|x| x.rvalue()).collect::<Vec<RValue<'a>>>());
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

    fn parse_call(
        &'a self,
        call: &mut structs::Call,
        field: Option<GccValues<'a>>,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) -> GccValues<'a> {
        let args = self.parse_params(&mut call.args, block, memory, ast);
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
        if call.name.name == "start_va" {
            let function = block.get_function();
            let last_fixed = function.get_param(std::cmp::max(1, function.get_param_count() as i32) - 1);
            let last_fixed_type = last_fixed.to_rvalue().get_type().get_aligned(8);
            let addr_type = memory.datatypes.get("ui8").unwrap();
            let offset = self.context.new_bitcast(None, last_fixed.to_lvalue().get_address(None), *addr_type);
            let offset = self.context.new_binary_op(None, BinaryOp::Plus, offset.get_type(), offset, self.context.new_rvalue_from_int(offset.get_type(), last_fixed_type.get_size() as i32));
            let variables = memory.variables.entry(memory.function_scope.clone()).or_insert(HashMap::new());
            let varargs = variables.get("varargs").unwrap();
            block.add_assignment(None, *varargs, self.context.new_bitcast(None, offset, varargs.to_rvalue().get_type()));
            return GccValues::L(*varargs);
        }
        if let Some(field) = field {
            return self.parse_impl_call(args, call, field, block, memory, ast);
        }
        let mut fn_name = call.name.name.clone();

        let mut to_impl = if let Some(to_impl) = memory.functions_with_traits.get(&fn_name) {
            fn_name = self.function_name(&to_impl.args.iter().collect(), &call.name.name);
            Some(to_impl.clone())
        }else{
            None
        };
        if let Some(ref to_impl) = to_impl {
            fn_name = self.function_name(&to_impl.args.iter().collect(), &call.name.name);
        }
        if !memory.functions.contains_key(&fn_name) && to_impl.is_none() {
            let mut function = ast
                .context
                .functions
                .get_mut(&fn_name)
                .expect(&format!("Couldn't find function {} on module {}", fn_name, ast.namespace))
                .clone();
            self.parse_function(&mut function, memory, ast);
        }else if let Some(ref mut to_impl) = to_impl {
            let params = self.build_impl_params(args.clone(), to_impl.args.clone(), memory, call.name.name.clone());
            let mut vars = HashMap::new();
            for i in 0..to_impl.args.len() {
                vars.insert(to_impl.args[i].name.name.clone(), params[i]);
            }
            let datatype = if let Some(ref mut dt) = to_impl.return_type {
                self.parse_datatype(dt, memory)
            }else{
                <() as Typeable>::get_type(self.context)
            };
            let function = self.context.new_function(None, gccjit::FunctionType::Internal, datatype, &params, fn_name.clone(), false);
            let entry = memory.variables.entry(fn_name.clone()).or_insert(vars.iter().map(|x| (x.0.clone(), x.1.to_lvalue())).collect());
            let last_param = function.get_param(function.get_param_count() as i32);
            entry.insert("#offset".into(), last_param.to_lvalue());
            memory.variadic_args.insert(function, params[to_impl.args.len()..].to_vec()) ;
            let mut new_block = function.new_block(self.uuid());
            let mut rc = self.get_rc_value(&mut to_impl.block).unwrap();
            let copy = memory.function_scope.clone();
            memory.function_scope = fn_name.clone();
            self.parse_block(&mut rc, &mut new_block, memory, ast);
            memory.function_scope = copy;
            memory.functions.insert(fn_name.clone(), function);
        }
        let function = memory.functions.get(&fn_name).expect(&format!("Couldn't find function {}", call.name.name)).clone();
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
        if left_type.is_compatible_with(rtn.get_type()) {
            return rtn;
        }
        if !left_type.is_compatible_with(rtn.get_type())
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
    ) -> GccValues<'a> {
        use structs::Operations;
        let mut value = self.get_rc_value(&mut unary_op.value).unwrap();
        let value = self.parse_value(&mut value, block, memory, ast);
        let op = match unary_op.prefix {
            Operations::Sub => Some(UnaryOp::Minus),
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
            if memory.should_delay_ref_ops {
                GccValues::L(*var)
            }else{
                self.access_name(var, name)
            }
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
