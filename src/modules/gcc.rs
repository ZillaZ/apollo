use gccjit::{
    BinaryOp, Block, ComparisonOp, Context, LValue, Parameter, RValue, ToLValue, ToRValue, Type,
    Typeable, UnaryOp,
};
use std::any::Any;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet, VecDeque};
use std::ops::DerefMut;
use std::rc::Rc;
use std::sync::Arc;

use super::ast_context::AstContext;
use super::memory::Memory;
use super::parser::{Ast, BuildCache};
use super::structs::{
    self, Arg, AssignVar, Condition, Constructor, DataType, Enum, EnumValue, FieldAccessName,
    ForLoop, Impl, ImplMethod, MacroKind, Name, Overloaded, OverloadedOp,
    RangeValue, RefOp, StructDecl, Value, ValueEnum,
};
use super::structs::{Expr, FunctionKind, LibLink, WhileLoop};
use crate::modules::structs::{ExpandSection, Otherwise, RangeType};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GccValues<'a> {
    L(LValue<'a>),
    R(RValue<'a>),
    Type(Type<'a>),
    Range(RValue<'a>),
    Nil,
}

impl<'a> GccValues<'a> {
    pub fn get_alignment(&self) -> i32 {
        match self {
            GccValues::L(lvalue) => lvalue.get_alignment(),
            GccValues::R(rvalue) => rvalue.dereference(None).get_alignment(),
            _ => 0,
        }
    }
    pub fn get_type(&self) -> Type<'a> {
        match self {
            GccValues::L(lvalue) => lvalue.to_rvalue().get_type(),
            GccValues::R(rvalue) => rvalue.get_type(),
            GccValues::Type(dt) => *dt,
            _ => unreachable!(),
        }
    }
    pub fn rvalue(&self) -> RValue<'a> {
        match self {
            GccValues::L(lvalue) => lvalue.to_rvalue(),
            GccValues::R(rvalue) | GccValues::Range(rvalue) => *rvalue,
            v => unreachable!("{:?}", v),
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
    functions_to_build: HashMap<String, structs::Function>,
    ast_context: AstContext,
}

impl<'a> GccContext<'a> {
    pub fn new(context: &'a Context<'a>, ast_context: AstContext) -> Self {
        let imports = HashSet::new();
        Self {
            imports,
            context,
            ast_context,
            functions_to_build: HashMap::new(),
        }
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
        r#type.get_pointee().is_some()
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
        let range_type = memory.datatypes.get("i4").unwrap().clone();
        let start = self.context.new_field(None, range_type, "start");
        let end = self.context.new_field(None, range_type, "end");
        let range = self
            .context
            .new_struct_type(None, "ApolloRange", &[start, end]);
        memory.datatypes.insert("#range".into(), range.as_type());
        memory.field_types.insert(start, range_type);
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
                    self.parse_enum(ast_enum, reference);
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
                Expr::Macro(ref apollo_macro) => {
                    memory.macros.push(apollo_macro.clone());
                }
                Expr::MacroCall(ref mut macro_call) => {
                    let result = self.parse_macro_call(macro_call, block, memory, ast);
                    block.add_eval(None, result.rvalue());
                }
                _ => continue,
            }
        }
    }

    fn parse_macro_call(
        &'a self,
        macro_call: &mut structs::Call,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) -> GccValues<'a> {
        if let Some((kind, expandable_macro)) =
            memory.expandable_macros.clone().get(&macro_call.name.name)
        {
            let macro_expressions = &expandable_macro.block.borrow_mut().expr;
            let ValueEnum::Closure(ref mut closure) = macro_call.args[0].value else {
                panic!("First argument of expandable macro call must be a closure")
            };
            let mut closure = self.get_rc_value(closure).unwrap();
            let closure_expressions = self.get_rc_value(&mut closure.block).unwrap().expr;
            let expr = match kind {
                ExpandSection::Head => vec![macro_expressions, &closure_expressions],
                ExpandSection::Tail => vec![&closure_expressions, macro_expressions],
            }
            .into_iter()
            .flatten()
            .map(|x| x.clone())
            .collect::<Vec<_>>();
            let box_return = match kind {
                ExpandSection::Head => closure.block.borrow_mut().box_return.clone(),
                ExpandSection::Tail => expandable_macro.block.borrow_mut().box_return.clone(),
            };
            let fn_name = format!(
                "closure_{}",
                self.uuid()
                    .chars()
                    .filter(|x| *x != '-')
                    .collect::<String>()
            );
            let dt = if let Some(ref mut dt) = expandable_macro.clone().return_type {
                self.parse_datatype(dt, memory)
            } else {
                <() as Typeable>::get_type(self.context)
            };
            let copy = memory.function_scope.clone();
            let mut count = 0;
            let mut parameters = Vec::new();
            let mut closure_vars = HashMap::new();
            let mut args = Vec::new();
            for (k, v) in memory.variables.get(&memory.function_scope).unwrap().iter() {
                args.push(v.to_rvalue());
                let parameter = self
                    .context
                    .new_parameter(None, v.to_rvalue().get_type(), k);
                parameters.push(parameter);
                count += 1;
                closure_vars.insert(k.into(), parameter.to_lvalue());
            }
            let closure = self.context.new_function(
                None,
                gccjit::FunctionType::Internal,
                dt,
                &parameters,
                &fn_name,
                false,
            );
            let mut new_block = closure.new_block(self.uuid());
            memory.variables.insert(fn_name.clone(), closure_vars);
            let mut closure_block = structs::Block { expr, box_return };
            memory.function_scope = fn_name;
            self.parse_block(&mut closure_block, &mut new_block, memory, ast);
            memory.function_scope = copy;
            return GccValues::R(self.context.new_call(None, closure, args.as_slice()));
        }
        GccValues::Nil
    }

    fn parse_asm(
        &'a self,
        asm: &structs::Assembly,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) {
        let extended = block.add_extended_asm(None, &asm.asm);
        extended.set_volatile_flag(asm.volatile);
        for arg in asm.input.iter() {
            let name = if let Some(ref name) = arg.name {
                Some(name.as_str())
            } else {
                None
            };
            extended.add_input_operand(
                name,
                &arg.constraint,
                self.parse_value(&mut Value::non_heap(arg.value.clone()), block, memory, ast)
                    .rvalue(),
            );
        }
        for arg in asm.output.iter() {
            let name = if let Some(ref name) = arg.name {
                Some(name.as_str())
            } else {
                None
            };
            extended.add_output_operand(
                name,
                &arg.constraint,
                self.parse_value(&mut Value::non_heap(arg.value.clone()), block, memory, ast)
                    .dereference(),
            );
        }
        for clob in asm.clobbered.iter() {
            extended.add_clobber(clob.as_str());
        }
    }

    fn parse_enum(&'a self, ast_enum: &mut Enum, memory: &mut Memory<'a>) {
        if memory.datatypes.contains_key(&ast_enum.name) {
            return;
        }
        let kind_type = *memory.datatypes.get("ui1").unwrap();
        let kind_field = self.context.new_field(None, kind_type, "kind");
        let mut field_index = 1;
        let mut fields = vec![];
        let mut map = HashMap::new();
        for variant in ast_enum.variants.iter_mut() {
            let mut field_value = None;
            if let Some(ref mut dt) = variant.r#type {
                let field_type = self.parse_datatype(dt, memory);
                let field = self
                    .context
                    .new_field(None, field_type, variant.name.as_str());
                field_value = Some(field);
                fields.push(field);
            }
            map.insert(variant.name.clone(), (field_index, field_value));
            field_index += 1;
        }
        let enum_type =
            self.context
                .new_union_type(None, format!(".{}", ast_enum.name.clone()), &fields);
        let union_field = self.context.new_field(None, enum_type, ".variants");
        let dt =
            self.context
                .new_struct_type(None, ast_enum.name.clone(), &[kind_field, union_field]);
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

    fn setup_impl_args(
        &'a self,
        name: String,
        method: &mut ImplMethod,
        memory: &mut Memory<'a>,
    ) -> Vec<Parameter<'a>> {
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
        memory.variables.insert(name, other_map);
        params
    }

    fn parse_impl_block(
        &'a self,
        implementation: &mut Impl,
        ast: &mut Ast,
        memory: &mut Memory<'a>,
    ) {
        let (target_type, target_name) = if let Some(ref target_name) = implementation.target_name {
            (
                memory.datatypes.get(target_name).unwrap().clone(),
                target_name.clone(),
            )
        } else {
            (
                memory
                    .datatypes
                    .get(&implementation.trait_name)
                    .unwrap()
                    .clone(),
                implementation.trait_name.clone(),
            )
        };
        let has_impl = {
            let implementations = memory.impls.entry(target_type).or_default();
            implementations.contains_key(&implementation.trait_name)
        };
        if !has_impl {
            self.impl_signature(implementation, memory);
        }
        let mut implementations = memory.impls.clone();
        let implementations = implementations.get_mut(&target_type).unwrap();
        let impl_map = implementations
            .entry(implementation.trait_name.clone())
            .or_default();
        for method in implementation.methods.iter_mut() {
            let fn_name = if method.name.contains(":") {
                method.name.clone()
            } else {
                format!("{target_name}:{}", method.name)
            };
            let function = impl_map.get(&fn_name).expect(&format!(
                "Method {} not found for {:?} implementation",
                fn_name, target_type
            ));
            let mut params = HashMap::new();
            for i in 0..function.get_param_count() {
                let param = function.get_param(i as i32);
                let ast_param = &method.params[i];
                params.insert(ast_param.name.name.clone(), param.to_lvalue());
            }
            let mut block = function.new_block(format!("{}_start", method.name));
            memory.variables.entry(fn_name.clone()).or_insert(params);
            let copy = memory.function_scope.clone();
            memory.function_scope = fn_name.clone();
            self.parse_block(&mut method.body, &mut block, memory, ast);
            memory.function_scope = copy;
            let entry = memory.impl_methods.entry(fn_name.clone()).or_default();
            entry.insert(target_type, *function);
            impl_map.insert(fn_name.clone(), *function);
        }
        let implementations = memory.impls.entry(target_type).or_default();
        implementations.insert(implementation.trait_name.clone(), impl_map.to_owned());
    }

    fn get_rc_value<T: Sized + Clone>(&self, rc: &mut Rc<RefCell<T>>) -> Option<T> {
        Rc::make_mut(rc).get_mut().clone().into()
    }

    fn inherit_tail_expr(&'a self, old: &Block<'a>, new: &Block<'a>, memory: &mut Memory<'a>) {
        if let Some(tail_expr) = memory.block_tail_expr.get(old) {
            memory.block_tail_expr.insert(*new, tail_expr.clone());
            memory.block_tail_expr.remove_entry(old);
        }
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
                } else {
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
                let condition = self
                    .context
                    .new_comparison(None, ComparisonOp::Equals, pivot, end);
                let mut loop_block = function.new_block(self.uuid());
                memory.blocks.insert(loop_block, false);
                let index = function.new_local(None, start.to_rvalue().get_type(), self.uuid());
                block.add_assignment(None, index, start.to_rvalue());
                let continue_block = function.new_block(self.uuid());
                self.inherit_tail_expr(&block, &loop_block, memory);
                let condition_block = function.new_block(self.uuid());
                condition_block.end_with_conditional(None, condition, continue_block, loop_block);
                let tail_expr = Expr::Overloaded(Overloaded {
                    lhs: structs::OverloadedLHS::Name(Name {
                        op: None,
                        op_count: 0,
                        name: fl.pivot.clone(),
                    }),
                    op: OverloadedOp::Add,
                    rhs: Value::non_heap(ValueEnum::Int(1)),
                });
                let entry = memory
                    .block_tail_expr
                    .entry(loop_block)
                    .or_insert(Vec::new());
                entry.push(tail_expr);
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
                    let impls = memory
                        .impls
                        .get(&value.to_rvalue().get_type())
                        .unwrap()
                        .clone();
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
                    self.inherit_tail_expr(&block, &continue_block, memory);
                    let condition_block = function.new_block(self.uuid());
                    condition_block.end_with_conditional(
                        None,
                        condition,
                        continue_block,
                        loop_block,
                    );
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
        self.inherit_tail_expr(&block, &continue_block, memory);
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

    fn build_fn_opaque(
        &'a self,
        fn_name: String,
        mut function: structs::Function,
        memory: &mut Memory<'a>,
    ) {
        let params = self.parse_args(&mut function.args, memory);
        let rtn_dt = if let Some(ref mut dt) = function.return_type {
            self.parse_datatype(dt, memory)
        } else {
            <() as Typeable>::get_type(self.context)
        };
        let function = self.context.new_function(
            None,
            gccjit::FunctionType::Internal,
            rtn_dt,
            &params,
            &fn_name,
            false,
        );
        memory.functions.insert(fn_name, function);
    }

    fn load_core(&'a self, memory: &mut Memory) {}

    fn setup_entry_point(
        &'a self,
        imports: &mut HashSet<String>,
        ast: &mut Ast,
        memory: &mut Memory<'a>,
        gen_types: bool,
    ) -> Block<'a> {
        if gen_types {
            self.gen_primitive_types(memory);
            self.gen_units(memory);
        }
        self.add_builtin_functions(memory);
        self.load_core(memory);
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
        self.context.dump_to_file(format!("{out}.c"), false);
        if is_debug {
            self.context
                .set_optimization_level(gccjit::OptimizationLevel::None);
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

    fn impl_signature(&'a self, implementation: &mut Impl, memory: &mut Memory<'a>) {
        let dt_name = if let Some(ref name) = implementation.target_name {
            name.clone()
        } else {
            implementation.trait_name.clone()
        };
        let target_dt = memory.datatypes.clone();
        let target_dt = target_dt.get(&dt_name).unwrap();
        for method in implementation.methods.iter_mut() {
            let dt = if let Some(ref mut dt) = method.datatype {
                self.parse_datatype(dt, memory)
            } else {
                <() as Typeable>::get_type(&self.context)
            };
            let parameters = self.parse_args(&mut method.params, memory);
            let fn_name = if method.name.contains(":") {
                method.name.clone()
            } else {
                format!("{dt_name}:{}", method.name)
            };
            let function = self.context.new_function(
                None,
                gccjit::FunctionType::Internal,
                dt,
                &parameters,
                fn_name.replace(":", "_"),
                false,
            );
            let entry = memory.impl_methods.entry(fn_name.clone()).or_default();
            entry.insert(*target_dt, function);
            let entry = memory.impls.entry(*target_dt).or_default();
            let entry = entry.entry(implementation.trait_name.clone()).or_default();
            entry.insert(fn_name.clone(), function);
        }
    }

    pub fn build_context(&'a self, _block: &mut Block<'a>, ast: &mut Ast, memory: &mut Memory<'a>) {
        println!(
            "STARTED BUILDING CONTEXT {} {:?}",
            ast.context.impls.get("char").unwrap().len(),
            ast.context
                .impls
                .get("char")
                .unwrap()
                .iter()
                .map(|x| &x.methods)
                .flatten()
                .map(|x| &x.name)
                .collect::<Vec<_>>()
        );
        for (_name, dt) in ast.context.structs.clone().iter_mut() {
            println!("BUILDING STRUCT {_name}");
            self.parse_struct(dt, memory);
        }
        for (_name, dt) in ast.context.enums.clone().iter_mut() {
            println!("BUILDING ENUM {_name}");
            self.parse_enum(dt, memory);
        }
        println!("STARTED BUILDING IMPLS");
        let mut parsed = HashSet::new();
        for (_name, implementations) in ast.context.impls.clone().iter_mut() {
            println!("IMPL FOR {_name}");
            for implementation in implementations.iter_mut() {
                if parsed.contains(&implementation.trait_name) {
                    continue;
                };
                parsed.insert(implementation.trait_name.clone());
                self.impl_signature(implementation, memory);
            }
        }
        parsed.clear();
        println!("FINISHED IMPLS");
        for (_, function) in ast.context.functions.clone().iter_mut() {
            self.parse_function_signature(function, memory, ast);
        }
        for (_name, implementations) in ast.context.impls.clone().iter_mut() {
            println!("IMPL FOR {_name}");
            for implementation in implementations.iter_mut() {
                if parsed.contains(&implementation.trait_name) {
                    continue;
                };
                parsed.insert(implementation.trait_name.clone());
                self.parse_impl(implementation, _block, ast, memory);
            }
        }
        for (_, function) in ast.context.functions.clone().iter_mut() {
            self.parse_function(function, memory, ast);
        }
    }

    pub fn gen_bytecode(
        &'a self,
        ast: &mut Ast,
        imports: &mut HashSet<String>,
        memory: &mut Memory<'a>,
        should_compile: bool,
        is_debug: bool,
        gen_types: bool,
        out: String,
    ) {
        let mut block = self.setup_entry_point(imports, ast, memory, gen_types);
        self.build_context(&mut block, ast, memory);
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
        let mut struct_type = if let Some(dt) = memory.datatypes.get(&r#struct.name) {
            let sdt = dt.is_struct().unwrap();
            if memory.opaque.contains(dt) {
                sdt.set_fields(None, fields.as_slice());
            }
            sdt
        } else {
            if fields.len() == 0 {
                let dt = self.context.new_opaque_struct_type(None, &r#struct.name);
                memory.opaque.insert(dt.as_type());
                dt
            } else {
                self.context
                    .new_struct_type(None, r#struct.name.clone(), &fields.as_slice())
            }
        };

        for attribute in r#struct.attributes.iter() {
            match attribute.name.as_str() {
                "alignment" => {
                    let ValueEnum::Int(bytes) = attribute.value else {
                        panic!()
                    };
                    let aligned = struct_type.as_type().get_aligned(bytes as u64);
                    struct_type = aligned.is_struct().unwrap();
                }
                _ => continue,
            }
        }
        memory.structs.insert(struct_type, new_struct);
        memory
            .datatypes
            .insert(r#struct.name.clone(), struct_type.as_type());
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
                    memory
                        .functions
                        .insert(name.trim_start_matches("_").to_string(), function);
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
        if let Some(ref tail_expr) = memory.block_tail_expr.get(block) {
            let mut ast = Ast {
                namespace: ast.namespace.clone(),
                expressions: tail_expr.to_vec(),
                imports: HashMap::new(),
                context: ast.context.clone(),
                core_context: ast.core_context.clone(),
            };
            self.parse_expression(&mut ast, memory, block);
            memory.block_tail_expr.remove_entry(&block);
        }
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
            ValueEnum::Closure(ref mut closure) => {
                let closure = closure.borrow_mut();
                let variables = memory.variables.get(&memory.function_scope).unwrap();
                let args = closure
                    .args
                    .iter()
                    .map(|x| (variables.get(x).unwrap(), x))
                    .collect::<Vec<(&LValue<'_>, &String)>>();
                let params = args
                    .iter()
                    .map(|(lvalue, name)| {
                        self.context
                            .new_parameter(None, lvalue.to_rvalue().get_type(), name)
                    })
                    .collect::<Vec<Parameter<'_>>>();
                let fn_name = self
                    .uuid()
                    .chars()
                    .filter(|x| *x != '-')
                    .collect::<String>();
                let function = self.context.new_function(
                    None,
                    gccjit::FunctionType::Internal,
                    <() as Typeable>::get_type(self.context),
                    &params,
                    format!("closure_{fn_name}"),
                    false,
                );
                let mut new_block = function.new_block(self.uuid());
                let mut block = closure.block.borrow_mut();
                self.parse_block(&mut block, &mut new_block, memory, ast);
                GccValues::R(function.get_address(None))
            }
            ref val => unreachable!("Found value enum {:?} while parsing value", val),
        };
        rtn
    }

    fn parse_enum_value(
        &'a self,
        enum_value: &mut Rc<RefCell<EnumValue>>,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) -> GccValues<'_> {
        let mut enum_value = self.get_rc_value(enum_value).unwrap();
        let datatype = memory.datatypes.get(&enum_value.datatype).unwrap().clone();
        let kind_field = datatype.is_struct().unwrap().get_field(0);
        let variant_field = datatype.is_struct().unwrap().get_field(1);
        let variants = memory.enum_variants.get(&datatype).unwrap().clone();
        let (index, active_field) = variants.get(&enum_value.variant).expect(&format!(
            "Tried to access variant {}, while variants for type {:?} are: {:?}",
            enum_value.variant, datatype, variants
        ));
        let function = block.get_function();
        let dummy = function.new_local(None, datatype, ".");
        let active_variant = dummy.access_field(None, kind_field);
        block.add_assignment(
            None,
            active_variant,
            self.context
                .new_rvalue_from_int(*memory.datatypes.get("ui1").unwrap(), *index),
        );
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
                let struct_type = *memory.datatypes.get("#range").unwrap();
                let struct_dt = struct_type.is_struct().unwrap();
                let start_field = struct_dt.get_field(0);
                let end_field = struct_dt.get_field(1);
                let start_dt = memory.field_types.get(&start_field).unwrap().clone();
                let start = self.new_cast(
                    start_dt,
                    &self.parse_value(&mut range.start, block, memory, ast),
                    memory,
                );
                let end = self.new_cast(
                    start_dt,
                    &self.parse_value(&mut range.end, block, memory, ast),
                    memory,
                );
                match range.range_type {
                    RangeType::Exclusive => {
                        let range = self.context.new_struct_constructor(
                            None,
                            struct_type,
                            Some(&[start_field, end_field]),
                            &[start.to_rvalue(), end.to_rvalue()],
                        );
                        GccValues::Range(range)
                    }
                    RangeType::Inclusive => {
                        let end = self.context.new_binary_op(
                            None,
                            BinaryOp::Plus,
                            end.to_rvalue().get_type(),
                            end.to_rvalue(),
                            self.context
                                .new_rvalue_from_int(end.to_rvalue().get_type(), 1),
                        );
                        let range = self.context.new_struct_constructor(
                            None,
                            struct_type,
                            Some(&[start_field, end_field]),
                            &[start.to_rvalue(), end],
                        );
                        GccValues::Range(range)
                    }
                }
            }
        }
    }

    fn root_value(&'a self, value: GccValues<'a>) -> LValue<'a> {
        match value {
            GccValues::L(mut lvalue) => {
                while lvalue.to_rvalue().get_type().get_pointee().is_some() {
                    lvalue = lvalue.to_rvalue().dereference(None)
                }
                lvalue
            }
            GccValues::R(rvalue) => {
                let mut lvalue = rvalue.dereference(None);
                while lvalue.to_rvalue().get_type().get_pointee().is_some() {
                    lvalue = rvalue.dereference(None)
                }
                lvalue
            }
            _ => unreachable!(),
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
                    let val = self.root_value(val);
                    let mut value = if let Some(field) = val.to_rvalue().get_type().is_struct() {
                        let struct_fields = memory
                            .structs
                            .get(&field)
                            .expect(&format!("Variable {:?} is not a struct, it has type {:?}. Tried to access field {}", val, field, name.name));
                        let field_index = struct_fields.get(&name.name).expect(&format!(
                            "Field {} does not exist on struct {:?}",
                            name.name, field
                        ));
                        let field = field.get_field(*field_index);
                        GccValues::L(val.access_field(None, field))
                    } else {
                        panic!(
                            "Tried to access {}, but {:?} is not a struct. It is {:?}",
                            name.name,
                            val,
                            val.to_rvalue().get_type()
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
                    if name.name[0..1] == name.name[0..1].to_uppercase() {
                        let dt = memory.datatypes.get(&name.name).expect(&format!(
                            "No datatype with name {} found. Defined types are {:?}",
                            name.name, memory.datatypes
                        ));
                        GccValues::Type(*dt)
                    } else {
                        let var = memory
                            .variables
                            .get(&memory.function_scope)
                            .expect(&format!(
                                "No memory created for function {}",
                                memory.function_scope
                            ))
                            .get(&name.name)
                            .expect(&format!(
                                "{} is not in scope for {}",
                                name.name, memory.function_scope
                            ));
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
                }
            },
            FieldAccessName::Call(ref mut call) => self.parse_call(call, aux, block, memory, ast),
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
        let rvalue = self.parse_value(&mut access.value, block, memory, ast);
        memory.should_delay_ref_ops = false;
        let index = self
            .parse_value(&mut access.index, block, memory, ast)
            .rvalue();
        if let ValueEnum::Name(ref name) = access.value.value {
            let access = self.context.new_array_access(None, rvalue.rvalue(), index);
            self.access_name(&access, name)
        } else {
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
        let DataType::Array(ref mut unit_type) = array.datatype.datatype else {
            panic!()
        };
        let mut unit_type = self.get_rc_value(unit_type).unwrap();
        let unit_type = self.parse_datatype(&mut unit_type.data_type, memory);
        let elements = array
            .elements
            .iter_mut()
            .map(|x| {
                let value = self.parse_value(x, block, memory, ast);
                if value.rvalue().get_type().is_compatible_with(unit_type) {
                    value.rvalue()
                } else {
                    self.new_cast(unit_type, &value, memory)
                }
            })
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
        let mut aux = ast_block.to_ast(
            ast.namespace.clone(),
            ast.context.clone(),
            ast.core_context.clone(),
        );
        self.parse_expression(&mut aux, memory, new_block);

        if let Some(ref mut rtn) = ast_block.box_return {
            self.build_return(rtn, new_block, memory, ast);
            return GccValues::R(
                self.context
                    .new_rvalue_from_int(<i32 as Typeable>::get_type(&self.context), 0),
            );
        } else {
            if let Some(ref tail_expr) = memory.block_tail_expr.get(new_block) {
                let mut ast = Ast {
                    namespace: ast.namespace.clone(),
                    expressions: tail_expr.to_vec(),
                    imports: HashMap::new(),
                    context: ast.context.clone(),
                    core_context: ast.core_context.clone(),
                };
                self.parse_expression(&mut ast, memory, new_block);
                memory.block_tail_expr.remove_entry(&new_block);
            }
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

    fn parse_function_signature(
        &'a self,
        function: &mut structs::Function,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) -> Option<gccjit::Function<'a>> {
        let mut expandable = false;
        for apollo_macro in memory.macros.iter() {
            for kind in apollo_macro.macros.iter() {
                match kind {
                    MacroKind::Align(_) => {
                        panic!("You're trying to align a function (??????) wtf bro")
                    }
                    MacroKind::Conditional(ref condition) => match condition {
                        Condition::Os(ref variant) => {
                            if !variant.is(std::env::consts::OS) {
                                memory.macros.clear();
                                return None;
                            }
                        }
                    },
                    MacroKind::Expand(ref expand) => {
                        expandable = true;
                        memory.expandable_macros.insert(
                            function.name.name.clone(),
                            (expand.clone(), function.clone()),
                        );
                    }
                    _ => unreachable!(),
                };
            }
        }
        memory.macros.clear();
        if expandable {
            return None;
        }
        if let Some(function) = memory.functions.get(&function.name.name) {
            return Some(*function);
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
        Some(new_function)
    }

    fn parse_function(
        &'a self,
        function: &mut structs::Function,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) {
        if let Some(new_function) = self.parse_function_signature(function, memory, ast) {
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
    }

    fn parse_args(
        &'a self,
        args: &mut Vec<structs::Arg>,
        memory: &mut Memory<'a>,
    ) -> Vec<Parameter<'a>> {
        let mut params = Vec::new();
        for arg in args.iter_mut() {
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
            DataType::UInt(bytecount) => {
                *memory.datatypes.get(&format!("ui{}", bytecount)).unwrap()
            }
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
                if let Some(val) = memory.datatypes.get(name) {
                    *val
                } else {
                    if let Some(decl) = self.ast_context.structs.clone().get(name) {
                        let mut decl = decl.clone();
                        self.parse_struct(&mut decl, memory);
                    } else if let Some(dt) = self.ast_context.enums.clone().get(name) {
                        let mut dt = dt.clone();
                        self.parse_enum(&mut dt, memory);
                    } else {
                        panic!("Datatype {name} does not exist")
                    }
                    *memory.datatypes.get(name).unwrap()
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
        let condition = if let Some(ref mut ast_condition) = ast_if.condition {
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
        } else {
            let enum_match = ast_if.enum_match.as_ref().unwrap();
            let vars = memory.variables.get(&memory.function_scope).unwrap();
            let var = vars.get(&enum_match.name).unwrap();
            let enum_type = var.to_rvalue().get_type().is_struct().unwrap();
            let variants = memory.enum_variants.get(&enum_type.as_type()).unwrap();
            let (index, field) = variants.get(&enum_match.variant).unwrap();
            let kind_field = enum_type.get_field(0);
            let variant_field = enum_type.get_field(1);
            let active_field = var.access_field(None, kind_field);
            let matching = self
                .context
                .new_rvalue_from_int(active_field.to_rvalue().get_type(), *index);
            let field_value = var.access_field(None, variant_field);
            tb_declared = Some((enum_match.var.clone(), (field_value, matching, field)));
            self.context
                .new_comparison(None, ComparisonOp::Equals, active_field, matching)
        };
        let function = block.get_function();
        let mut then_block = function.new_block(self.uuid());
        let mut ast_block = self.get_rc_value(&mut ast_if.block).unwrap();
        if let Some((ref name, (value, index, field))) = tb_declared {
            let value = if let Some(field) = field {
                value.access_field(None, *field).to_rvalue()
            } else {
                index
            };
            let local = function.new_local(None, value.to_rvalue().get_type(), name);
            let vars = memory.variables.get_mut(&memory.function_scope).unwrap();
            vars.insert(name.clone(), local);
            then_block.add_assignment(None, local, value.to_rvalue());
        }
        self.parse_block(&mut ast_block, &mut then_block, memory, ast);
        let mut else_should_continue = false;
        let mut else_block = function.new_block(self.uuid());
        block.end_with_conditional(None, condition, then_block, else_block);
        self.inherit_tail_expr(&block, &else_block, memory);
        if let Some(ref mut otherwise) = ast_if.otherwise {
            let mut otherwise = self.get_rc_value(otherwise).unwrap();
            match otherwise {
                Otherwise::Block(ref mut block) => {
                    else_should_continue = block.box_return.is_none();
                    self.parse_block(block, &mut else_block, memory, ast);
                }
                Otherwise::If(ref mut ast_if) => {
                    let block = self.get_rc_value(&mut ast_if.block).unwrap();
                    else_should_continue = block.box_return.is_none();
                    else_block = self.parse_if(ast_if, &mut else_block, memory, ast);
                }
            }
        };
        let ast_block = self.get_rc_value(&mut ast_if.block).unwrap();
        let else_block = if else_should_continue {
            let new = function.new_block(self.uuid());
            else_block.end_with_jump(None, new);
            new
        } else {
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
            let variables = memory
                .variables
                .get_mut(&memory.function_scope)
                .expect(&format!(
                    "Variable {} not found on {:?}",
                    declaration.name.name, memory.function_scope
                ));
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

    fn size_of(&'a self, block: Block<'a>, value: &GccValues<'a>, memory: &mut Memory<'a>) -> RValue<'a> {
        let function = block.get_function();
        let arr = self.context.new_array_type(None, value.get_type(), 2);
        let aux = self.context.new_array_constructor(None, arr, &[value.rvalue(), value.rvalue()]);
        let bind = function.new_local(None, arr, self.uuid());
        block.add_assignment(None, bind, aux);
        let dt = memory.datatypes.get("i8").unwrap();
        let one = self.context.new_array_access(None, bind, self.context.new_rvalue_from_int(*dt, 0)).get_address(None);
        let two = self.context.new_array_access(None, bind, self.context.new_rvalue_from_int(*dt, 1)).get_address(None);
        let one = self.context.new_bitcast(None, one, *dt);
        let two = self.context.new_bitcast(None, two, *dt);
        self.context.new_binary_op(None, BinaryOp::Minus, *dt, two, one)
    }

    fn build_impl_params(
        &'a self,
        mut args: Vec<GccValues<'a>>,
        mut params: Vec<structs::Arg>,
        memory: &mut Memory<'a>,
        name: String,
    ) -> Vec<Parameter<'a>> {
        let len = params.len();
        let mut rtn = vec![];
        for i in 0..len {
            let param = &mut params[i];
            let arg = &mut args[i];

            rtn.push(
                self.context
                    .new_parameter(None, arg.rvalue().get_type(), &param.name.name),
            );
        }
        rtn
    }

    fn root_type(&'a self, dt: Type<'a>) -> Type<'a> {
        let mut rtn = dt;
        while let Some(val) = rtn.get_pointee() {
            rtn = val
        }
        rtn
    }

    fn parse_impl_call(
        &'a self,
        partial_args: Vec<GccValues<'a>>,
        call: &mut structs::Call,
        field: GccValues<'a>,
        block: &mut Block<'a>,
        memory: &mut Memory<'a>,
        ast: &mut Ast,
    ) -> GccValues<'a> {
        let dt = self.root_type(match field {
            GccValues::R(rvalue) => rvalue.get_type(),
            GccValues::L(lvalue) => lvalue.to_rvalue().get_type(),
            GccValues::Type(dt) => dt,
            _ => unreachable!(),
        });
        let mut args = if let GccValues::Type(_) = field {
            vec![]
        } else {
            vec![field.clone()]
        };
        args.extend(partial_args);
        let (dt_name, _) = memory
            .datatypes
            .iter()
            .find(|x| *x.1 == dt)
            .expect(&format!("Datatype {:?} does not exists", dt));
        let mut fn_name = format!("{dt_name}:{}", call.name.name.clone());
        /*
        println!(
            "Impls for {:?}: {:?}",
            dt,
            memory.impl_methods.get(&fn_name)
        );
         *
         */
        let method = {
            let aux = memory.datatypes.clone();
            let (name, _) = aux.iter().find(|(_, v)| **v == dt).unwrap();
            let impls = ast
                .context
                .impls
                .get(name)
                .expect(&format!("No implementations found for type {name}"));
            let method = impls
                .iter()
                .map(|x| &x.methods)
                .flatten()
                .find(|x| x.name == *fn_name)
                .expect(&format!("Method {} not found for {:?}", fn_name, dt));
            let mut method = method.clone();
            let params = self.parse_args(&mut method.params, memory);
            let dt = if let Some(dt) = method.datatype {
                self.parse_datatype(&mut structs::Type::from(dt), memory)
            } else {
                <() as Typeable>::get_type(self.context)
            };
            self.context.new_function(
                None,
                gccjit::FunctionType::Internal,
                dt,
                &params,
                fn_name,
                false,
            )
        };
        for i in 0..args.len() {
            if method.get_param_count() <= i {
                break;
            }
            let declared_type = method.get_param(i as i32).to_rvalue().get_type();
            let aref = args[i].clone();
            let parameter = args.get_mut(i).unwrap();
            *parameter = GccValues::R(self.new_cast(declared_type, &aref, memory));
        }
        let value = self.context.new_call(
            None,
            method,
            &args.iter().map(|x| x.rvalue()).collect::<Vec<RValue<'a>>>(),
        );
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
            return GccValues::R(self.size_of(*block, &args[0], memory));
        }
        if let Some(field) = field {
            return self.parse_impl_call(args, call, field, block, memory, ast);
        }

        let fn_name = call.name.name.clone();
        if !memory.functions.contains_key(&fn_name) {
            let mut functions = ast.context.functions.clone();
            let mut function = functions.get_mut(&fn_name);
            if let Some(ref mut function) = function {
                let function = self
                    .parse_function_signature(function, memory, ast)
                    .unwrap();
                memory.functions.insert(fn_name.clone(), function);
            }
        }
        let function = memory
            .functions
            .get(&fn_name)
            .expect(&format!(
                "Couldn't find function {}. Defined functions are {:?}",
                call.name.name, memory.functions
            ))
            .clone();
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
        let left_is_ptr = self.is_pointer(&left_type, memory);
        let left_is_numeric = left_type.is_integral();
        let right_is_ptr = self.is_pointer(&rtn.get_type(), memory);
        if (left_type.is_compatible_with(*memory.datatypes.get("Any").unwrap()) || left_is_ptr)
            && !right_is_ptr
        {
            rtn = self
                .context
                .new_cast(None, right.get_reference(), left_type);
        } else if !left_is_ptr && !left_is_numeric && right_is_ptr {
            rtn = self.context.new_cast(None, right.dereference(), left_type);
        } else if left_is_numeric && right_is_ptr {
            rtn = self.context.new_bitcast(None, rtn, left_type);
        } else {
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
            Operations::BitshiftLeft => Helper::Binary(BinaryOp::LShift),
            Operations::BitshiftRight => Helper::Binary(BinaryOp::RShift),
            Operations::BitOr => Helper::Binary(BinaryOp::BitwiseOr),
            Operations::BitAnd => Helper::Binary(BinaryOp::BitwiseAnd),
            Operations::BitXor => Helper::Binary(BinaryOp::BitwiseXor),
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
            } else {
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
