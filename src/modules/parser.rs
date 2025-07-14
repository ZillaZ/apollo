use super::super::Program;
use super::ast_context::AstContext;
use crate::{modules::structs::*, Rule};
use pest::Parser;
use pest::{
    iterators::{Pair, Pairs},
    pratt_parser::{Assoc, Op, PrattParser},
};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub struct Ast {
    pub namespace: String,
    pub expressions: Vec<Expr>,
    pub imports: HashMap<(String, Import), Rc<RefCell<Ast>>>,
    pub context: AstContext,
    pub core_context: AstContext,
}

impl Ast {
    pub fn extend(&mut self, new: &Ast) {
        self.expressions = vec![new.expressions.clone(), self.expressions.clone()].into_iter().flatten().collect();
        self.context.extend(&new.context);
        self.core_context = new.context.clone();
        extend_imports(&mut self.imports, new);
    }

    pub fn build_imports(&mut self) {
        for ((_path, import), v) in self.imports.iter_mut() {
            let mut ast = v.borrow_mut();
            ast.build_imports();
            for import in parse_import_path(import) {
                let import = import.split("/").last().unwrap();
                println!("building import {}", import);
                if let Some(function) = ast.context.functions.clone().get(import) {
                    let mut rec_imports = ast.get_fn_dependencies(import);
                    for expr in rec_imports.iter() {
                        match expr {
                            Expr::StructDecl(ref decl) => {
                                self.context.structs.insert(decl.name.clone(), decl.clone());
                            }
                            Expr::Function(ref function) => {
                                self.context.functions.insert(function.name.name.clone(), function.clone());
                            }
                            _ => unreachable!()
                        }
                    }
                    rec_imports.push(Expr::Function(function.clone()));
                    rec_imports.extend_from_slice(&self.expressions);
                    self.expressions = rec_imports;
                    self.context.functions.insert(function.name.name.clone(), function.clone());
                }else if let Some(dt) = ast.context.structs.clone().get(import) {
                    let (mut rec_imports, impls) = ast.get_struct_dependencies(import);
                    for expr in rec_imports.iter() {
                        let mut aux = vec![expr.clone()];
                        aux.extend_from_slice(&self.expressions);
                        self.expressions = aux;

                        match expr {
                            Expr::StructDecl(ref decl) => {
                                self.context.structs.insert(decl.name.clone(), decl.clone());
                            }
                            Expr::Enum(ref dt) => {
                                self.context.enums.insert(dt.name.clone(), dt.clone());
                            }
                            _ => continue
                        };
                    }
                    rec_imports.push(Expr::StructDecl(dt.clone()));
                    rec_imports.extend_from_slice(&impls);
                    rec_imports.extend_from_slice(&self.expressions);
                    self.expressions = rec_imports;
                    self.context.structs.insert(dt.name.clone(), dt.clone());
                    self.context.impls.insert(dt.name.clone(), impls.clone().into_iter().map(|x| if let Expr::Impl(i) = x { i } else { unreachable!() }).collect());
                }else if let Some(dt) = ast.context.enums.clone().get(import) {
                    let (mut rec_imports, impls) = ast.get_enum_dependencies(import);
                    for expr in rec_imports.iter() {
                        let mut aux = vec![expr.clone()];
                        aux.extend_from_slice(&self.expressions);
                        self.expressions = aux;

                        match expr {
                            Expr::StructDecl(ref decl) => {
                                self.context.structs.insert(decl.name.clone(), decl.clone());
                            }
                            Expr::Enum(ref dt) => {
                                self.context.enums.insert(dt.name.clone(), dt.clone());
                            }
                            _ => continue
                        };
                    }
                    rec_imports.push(Expr::Enum(dt.clone()));
                    rec_imports.extend_from_slice(&impls);
                    rec_imports.extend_from_slice(&self.expressions);
                    self.expressions = rec_imports;
                    self.context.enums.insert(dt.name.clone(), dt.clone());
                    self.context.impls.insert(dt.name.clone(), impls.clone().into_iter().map(|x| if let Expr::Impl(i) = x { i } else { unreachable!() }).collect());
                }
            }
        }
    }

    pub fn get_enum_dependencies(&mut self, import: &str) -> (Vec<Expr>, Vec<Expr>) {
        let mut rtn = Vec::new();
        let mut impls = Vec::new();
        let dt = self.context.enums.get(import).unwrap();
        for variant in dt.variants.iter() {
            if let Some(ref dt) = variant.r#type {
                match dt.datatype {
                    DataType::StructType(ref name) => {
                        if let Some(dt) = self.context.structs.get(name) {
                            rtn.push(Expr::StructDecl(dt.clone()));
                        }else{
                            let dt = self.context.enums.get(name).unwrap();
                            rtn.push(Expr::Enum(dt.clone()));
                        }
                        if let Some(aimpls) = self.context.impls.get(name) {
                            impls = aimpls.clone().into_iter().map(|x| Expr::Impl(x)).collect();
                        }
                    }
                    _ => continue
                }
            }
        }
        if let Some(aimpls) = self.context.impls.get(import) {
            impls.extend(aimpls.iter().map(|x| Expr::Impl(x.clone())));
        }
        (rtn, impls)
    }

    pub fn get_struct_dependencies(&mut self, import: &str) -> (Vec<Expr>, Vec<Expr>) {
        let mut rtn = Vec::new();
        let mut impls = Vec::new();
        let dt = self.context.structs.get(import).unwrap();
        for field in dt.fields.iter() {
            match field.datatype.datatype {
                DataType::StructType(ref name) => {
                    if let Some(dt) = self.context.structs.get(name) {
                        rtn.push(Expr::StructDecl(dt.clone()));
                    }else{
                        let dt = self.context.enums.get(name).expect(&format!("Enum {} isn't defined", name));
                        rtn.push(Expr::Enum(dt.clone()));
                    }
                    if let Some(aimpls) = self.context.impls.get(name) {
                        println!("has impl {:?}", aimpls);
                        impls = aimpls.clone().into_iter().map(|x| Expr::Impl(x)).collect();
                    }
                }
                _ => continue
            }
        }

        if let Some(aimpls) = self.context.impls.get(import) {
            println!("ISS IMPL {:?}", aimpls);
            impls.extend(aimpls.iter().map(|x| Expr::Impl(x.clone())));
        }
        (rtn, impls)
    }

    pub fn get_fn_dependencies(&mut self, import: &str) -> Vec<Expr> {
        let mut rtn = Vec::new();
        let function = self.context.functions.get(import).unwrap();
        for param in function.args.iter() {
            if let ParameterType::Type(ref dt) = param.datatype {
                match dt.datatype {
                    DataType::StructType(ref dt_name) => {
                        let dt = self.context.structs.get(dt_name).unwrap();
                        rtn.push(Expr::StructDecl(dt.clone()));
                    }
                    _ => continue
                }
            }
        }
        if let Some(ref dt) = function.return_type {
            match dt.datatype {
                DataType::StructType(ref name) => {
                    let dt = self.context.structs.get(name).unwrap();
                    rtn.push(Expr::StructDecl(dt.clone()));
                }
                _ => ()
            }
        }

        let block = function.block.borrow();
        for expr in block.expr.iter() {
            let expr = expr.borrow();
            match *expr {
                Expr::Call(ref call) => {
                    if self.context.functions.contains_key(&call.name.name) {
                        continue
                    }
                    if let Some(function) = self.context.functions.get(&call.name.name) {
                        rtn.push(Expr::Function(function.clone()));
                    }else{
                        println!("Function {} isn't defined. Skipping...", call.name.name);
                    }
                },
                Expr::Assignment(ref assignment) => {
                    if let ValueEnum::Constructor(ref constructor) = assignment.value.value {
                        let constructor = constructor.borrow();
                        let dt = self.context.structs.get(&constructor.name).unwrap();
                        rtn.push(Expr::StructDecl(dt.clone()));
                    }
                },
                _ => continue
            }
        }
        rtn
    }
}

fn parse_import_path(import: &Import) -> Vec<String> {
    fn recursive_descent(namespace: &Namespace, acc: String, paths: &mut Vec<String>) {
        if namespace.next.is_empty() {
            paths.push(format!("{acc}/{}", namespace.name));
        }else{
            for namespace in namespace.next.iter() {
                let acc = if namespace.next.is_empty() {
                    acc.clone()
               }else{
                    format!("{acc}/{}", namespace.name)
                };
                recursive_descent(namespace, acc, paths);
            }
        }
    }
    let mut paths = vec![];
    let start = if import.namespace.name == "std" {
        std::env::var("APOLLO_LIBS").unwrap()
                            }else{
        std::env::current_dir().unwrap().to_str().unwrap().to_string()
    };
    recursive_descent(&import.namespace, start, &mut paths);
    paths
}
fn extend_imports(imports: &mut HashMap<(String, Import), Rc<RefCell<Ast>>>, new: &Ast) {
    imports.iter_mut().for_each(|(_, ast)| {
        let mut ast = ast.borrow_mut();
        ast.extend(new);
    });
}

pub struct NoirParser {
    pub pratt_parser: PrattParser<Rule>,
}

impl NoirParser {
    pub fn new() -> Self {
        let pratt_parser = PrattParser::new()
            .op(Op::prefix(Rule::neg))
            .op(Op::infix(Rule::bt_left, Assoc::Left) | Op::infix(Rule::bt_right, Assoc::Left) | Op::infix(Rule::bt_or, Assoc::Left) | Op::infix(Rule::bt_and, Assoc::Left) | Op::infix(Rule::bt_xor, Assoc::Left))
            .op(Op::infix(Rule::add, Assoc::Left) | Op::infix(Rule::sub, Assoc::Left))
            .op(Op::infix(Rule::mul, Assoc::Left) | Op::infix(Rule::div, Assoc::Left))
            .op(Op::infix(Rule::and, Assoc::Left))
            .op(Op::infix(Rule::or, Assoc::Left)
                | Op::infix(Rule::neq, Assoc::Left)
                | Op::infix(Rule::gt, Assoc::Left)
                | Op::infix(Rule::lt, Assoc::Left)
                | Op::infix(Rule::gte, Assoc::Left)
                | Op::infix(Rule::lte, Assoc::Left)
                | Op::infix(Rule::cmp_eq, Assoc::Left))
            .op(Op::infix(Rule::modulo, Assoc::Left))
            .op(Op::prefix(Rule::not));
        Self { pratt_parser }
    }

    pub fn gen_ast(&self, pairs: &mut Pairs<Rule>, namespace: String) -> Ast {
        let namespace = namespace.split("::").last().unwrap().to_string();
        let mut context = AstContext::new();
        context.scope = "main".to_string();
        let expressions = self.build_expression(pairs, &mut context);
        let imports = expressions
            .iter()
            .filter(|x| match x {
                Expr::Import(_) => true,
                _ => false,
            })
            .map(|x| x.import())
            .collect::<Vec<Import>>();
        let imports = self.load_imports(&imports, &mut context);

        Ast {
            namespace,
            expressions,
            context,
            imports,
            core_context: AstContext::new()
        }
    }

    fn load_imports(
        &self,
        imports: &Vec<Import>,
        context: &mut AstContext,
    ) -> HashMap<(String, Import), Rc<RefCell<Ast>>> {
        let mut rtn = HashMap::new();
        for import in imports {
            let lib_paths = self.parse_import_path(&import);
            for lib_path in lib_paths.iter().map(|x| {
                let mut aux : Vec<String> = x.split("/").map(|x| x.to_string()).collect();
                aux.pop();
                aux.join("/")
            }) {
                let new_name = lib_path.split("/").collect::<Vec<&str>>().join("::");
                let lib_path = format!("{}.apo", lib_path);
                let input = std::fs::read_to_string(lib_path.clone()).unwrap();
                let mut pairs: Pairs<Rule> = Program::parse(Rule::program, &input).unwrap();
                let ast = self.gen_ast(&mut pairs, new_name);

                rtn.insert((lib_path, import.clone()), Rc::new(RefCell::new(ast)));
            }
        }
        rtn
    }

    fn parse_import_path(&self, import: &Import) -> Vec<String> {
        fn recursive_descent(namespace: &Namespace, acc: String, paths: &mut Vec<String>) {
            if namespace.next.is_empty() {
                paths.push(format!("{acc}/{}", namespace.name));
            }else{
                for namespace in namespace.next.iter() {
                    let acc = if namespace.next.is_empty() {
                        acc.clone()
                    }else{
                        format!("{acc}/{}", namespace.name)
                    };
                    recursive_descent(namespace, acc, paths);
                }
            }
        }
        let mut paths = vec![];
        let start = if import.namespace.name == "std" {
            std::env::var("APOLLO_LIBS").unwrap()
        }else{
            std::env::current_dir().unwrap().to_str().unwrap().to_string()
        };
        recursive_descent(&import.namespace, start, &mut paths);
        paths
    }

    fn build_expression(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Vec<Expr> {
        let mut expressions = Vec::new();

        for pair in pairs {
            let expr = match pair.as_rule() {
                Rule::r#return => Expr::Return(self.build_return(&mut pair.into_inner(), context)),
                Rule::call => Expr::Call(self.build_call(&mut pair.into_inner(), context)),
                Rule::macro_call => Expr::MacroCall(self.build_call(&mut pair.into_inner(), context)),
                Rule::function => {
                    Expr::Function(self.build_function(&mut pair.into_inner(), context))
                }
                Rule::block => Expr::Block(self.build_block(&mut pair.into_inner(), context)),
                Rule::declaration => {
                    Expr::Declaration(self.build_declaration(&mut pair.into_inner(), context))
                }
                Rule::r#if => Expr::If(self.build_if(&mut pair.into_inner(), context)),
                Rule::assignment => {
                    Expr::Assignment(self.build_assignment(&mut pair.into_inner(), context))
                }
                Rule::overloaded_op => {
                    Expr::Overloaded(self.build_overloaded(&mut pair.into_inner(), context))
                }
                Rule::import => Expr::Import(self.build_import(&mut pair.into_inner(), context)),
                Rule::r#struct => {
                    Expr::StructDecl(self.build_struct(&mut pair.into_inner(), context))
                }
                Rule::field_access => {
                    Expr::FieldAccess(self.build_field_access(&mut pair.into_inner(), context))
                }
                Rule::r#trait => Expr::Trait(self.build_trait(&mut pair.into_inner(), context)),
                Rule::lib_link => Expr::Link(self.build_link(&mut pair.into_inner())),
                Rule::r#while => {
                    Expr::While(self.build_while_loop(&mut pair.into_inner(), context))
                }
                Rule::r#for => Expr::For(self.build_for_loop(&mut pair.into_inner(), context)),
                Rule::r#impl => Expr::Impl(self.build_impl(&mut pair.into_inner(), context)),
                Rule::r#enum => Expr::Enum(self.build_enum(&mut pair.into_inner(), context)),
                Rule::assembly => Expr::Assembly(self.build_assembly(&mut pair.into_inner(), context)),
                Rule::variadic_block => Expr::VariadicBlock(self.build_block(&mut pair.into_inner(), context)),
                Rule::r#macro => Expr::Macro(self.build_macro(&mut pair.into_inner(), context)),
                Rule::EOI => continue,
                rule => unreachable!("{:?}", rule),
            };
            expressions.push(expr);
        }
        expressions
    }

    fn build_macro(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Macro {
        let mut macros = Vec::new();
        for pair in pairs {
            match pair.as_rule() {
                Rule::attribute => macros.push(self.build_macro_attribute(&mut pair.into_inner(), context)),
                _ => unreachable!()
            }
        }
        Macro { macros }
    }

    fn build_assembly(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Assembly {
        let mut string = String::new();
        let mut input = vec![];
        let mut output = vec![];
        let mut clob = vec![];
        let mut volatile = false;
        for pair in pairs {
            match pair.as_rule() {
                Rule::volatile => volatile = true,
                Rule::string => string = pair.as_str()[1..pair.as_str().len()-1].into(),
                Rule::asm_in => input = self.build_asm_args(&mut pair.into_inner(), context),
                Rule::asm_out => output = self.build_asm_args(&mut pair.into_inner(), context),
                Rule::asm_clob => clob = pair.into_inner().map(|x| x.as_str()[1..x.as_str().len()-1].to_string()).collect(),
                _ => unreachable!()
            }
        }
        Assembly { volatile, asm: string, input, output, clobbered: clob }
    }

    fn build_asm_args(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Vec<AsmArg> {
        let mut rtn = vec![];
        for pair in pairs {
            let mut string = String::new();
            let mut name = None;
            let mut val = ValueEnum::Int(0);
            for mut eval in pair.into_inner() {
                match eval.as_rule() {
                    Rule::string => string = eval.as_str()[1..eval.as_str().len()-1].into(),
                    Rule::bvalue | Rule::base_value | Rule::binary_operation | Rule::unary_operation => val = self.build_single_value(&mut eval, context).value,
                    Rule::name => name = Some(self.build_name(&mut eval.into_inner(), context).name),
                    _ => unreachable!()
                }
            }
            rtn.push(AsmArg{ constraint: string, value: val, name })
        }
        rtn
    }

    fn build_enum(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Enum {
        let mut name = String::new();
        let mut variants = vec![];
        for pair in pairs {
            match pair.as_rule() {
                Rule::struct_type => name = pair.as_str().to_string(),
                Rule::enum_variant => variants.push(self.build_enum_variant(&mut pair.into_inner(), context)),
                _ => unreachable!()
            }
        }
        let ast_enum = Enum {
            name, variants
        };
        context.enums.insert(ast_enum.name.clone(), ast_enum.clone());
        ast_enum
    }

    fn build_enum_variant(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> EnumVariant {
        let mut name = String::new();
        let mut r#type =  None;
        for pair in pairs {
            match pair.as_rule() {
                Rule::struct_type => name = pair.as_str().into(),
                Rule::datatype => r#type = Some(self.build_datatype(&mut pair.into_inner(), context)),
                _ => unreachable!()
            }
        }
        EnumVariant { name, r#type }
    }

    fn build_impl(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Impl {
        let mut switched = false;
        let mut trait_name = String::new();
        let mut target_name : Option<String> = None;
        let mut methods = vec![];
        let mut generics = vec![];
        for pair in pairs {
            match pair.as_rule() {
                Rule::name => {
                    if switched {
                        target_name = Some(pair.as_str().into());
                    } else {
                        trait_name = pair.as_str().into();
                    }
                }
                Rule::impl_for => switched = true,
                Rule::impl_block => (generics, methods) = self.build_impl_block(&mut pair.into_inner(), context),
                _ => todo!(),
            }
        }
        let name: String = if let Some(ref target_name) = target_name {
            target_name.clone()
        }else{
            trait_name.clone()
        };

        let implementation = Impl {
            trait_name,
            target_name,
            generics,
            methods,
        };
        let entry = context.impls.entry(name).or_insert(Vec::new());
        entry.push(implementation.clone());
        implementation
    }

    fn build_impl_block(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> (Vec<(String, String)>, Vec<ImplMethod>) {
        let mut generics = vec![];
        let mut methods = vec![];
        for pair in pairs {
            match pair.as_rule() {
                Rule::function => methods.push(self.build_impl_method(&mut pair.into_inner(), context)),
                Rule::impl_type => {
                    let mut inner = pair.into_inner();
                    let key = inner.next().unwrap().as_str().to_string();
                    let value = inner.next().unwrap().as_str().to_string();
                    generics.push((key, value));
                },
                _ => unreachable!()
            };
        }
        (generics, methods)
    }

    fn build_impl_method(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> ImplMethod {
        let mut name = String::new();
        let mut params = vec![];
        let mut datatype = None;
        let mut body = Block::default();
        for pair in pairs {
            match pair.as_rule() {
                Rule::name => name = pair.as_str().into(),
                Rule::datatype => datatype = Some(self.build_datatype(&mut pair.into_inner(), context)),
                Rule::args => params = self.build_args(&mut pair.into_inner(), context),
                Rule::block => body = self.build_block(&mut pair.into_inner(), context),
                _ => unreachable!()
            }
        }
        ImplMethod { name, params, datatype, body }
    }

    fn build_impl_type(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> ImplType {
        let mut name = String::new();
        let mut implements = vec![];
        let mut switched = false;
        for pair in pairs {
            match pair.as_rule() {
                Rule::name => if switched { implements.push(pair.as_str().to_string()) } else { name = pair.as_str().to_string(); switched = true },
                _ => unreachable!()
            }
        }
        ImplType { name, implements }
    }

    fn build_for_loop(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> ForLoop {
        let mut pivot = String::new();
        let mut range = Value::default();
        let mut block = Block::default();
        for pair in pairs {
            match pair.as_rule() {
                Rule::name => pivot = pair.as_str().to_string(),
                Rule::bvalue => range = self.build_bvalue(&mut pair.into_inner(), context),
                Rule::binary_operation => {
                    range = self.build_binary_op(&mut pair.into_inner(), context)
                }
                Rule::block => block = self.build_block(&mut pair.into_inner(), context),
                rule => unreachable!("Found rule {:?} while building for loop", rule),
            }
        }
        ForLoop {
            pivot,
            range,
            block,
        }
    }

    fn build_while_loop(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> WhileLoop {
        let mut condition = Value::default();
        let mut block = Block::default();
        for mut pair in pairs {
            match pair.as_rule() {
                Rule::bvalue
                | Rule::base_value
                | Rule::unary_operation
                | Rule::binary_operation => condition = self.build_single_value(&mut pair, context),
                Rule::block => block = self.build_block(&mut pair.into_inner(), context),
                rule => unreachable!("Found rule {:?} while building while loop", rule),
            }
        }
        WhileLoop {
            condition,
            block: Rc::new(RefCell::new(block)),
        }
    }

    fn build_link(&self, pairs: &mut Pairs<Rule>) -> LibLink {
        let mut eval = pairs.peekable();
        let eval = eval.peek().unwrap();
        LibLink {
            lib_name: eval.as_str()[1..eval.as_str().len() - 1].trim().into(),
        }
    }

    fn build_trait(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Trait {
        let mut name = String::new();
        let mut methods = Vec::new();
        let mut generics = Vec::new();
        for pair in pairs {
            match pair.as_rule() {
                Rule::name_str => name = pair.as_str().into(),
                Rule::trait_decl => {
                    let next = pair.into_inner().next().unwrap();
                    match next.as_rule() {
                        Rule::trait_function => methods.push(self.build_trait_method(&mut next.into_inner(), context)),
                        Rule::trait_generic_type => generics.push(next.into_inner().next().unwrap().as_str().into()),
                        _ => unreachable!()
                    }
                }
                _ => unreachable!(),
            }
        }
        Trait { name, generics, methods }

    }

    fn build_trait_method(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> TraitMethod {
        let mut name = String::new();
        let mut params = vec![];
        let mut datatype = None;
        for pair in pairs {
            match pair.as_rule() {
                Rule::name_str => name = pair.as_str().into(),
                Rule::parameter => params.push(self.build_param(&mut pair.into_inner(), context)),
                Rule::datatype => datatype = Some(self.build_datatype(&mut pair.into_inner(), context)),
                _ => unreachable!()
            }
        }
        TraitMethod { name, params, datatype }
    }

    fn build_field_decl(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> FieldDecl {
        let mut name = String::new();
        let mut datatype = Type {
            is_ref: false,
            ref_count: 0,
            datatype: DataType::Int(0),
        };
        for pair in pairs {
            match pair.as_rule() {
                Rule::name_str => name = pair.as_str().into(),
                Rule::datatype => datatype = self.build_datatype(&mut pair.into_inner(), context),
                _ => unreachable!(),
            }
        }
        FieldDecl { name, datatype }
    }

    fn build_struct(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> StructDecl {
        let mut name = String::new();
        let mut fields = Vec::new();
        let mut attributes = Vec::new();
        for pair in pairs {
            match pair.as_rule() {
                Rule::name_str => name = pair.as_str().into(),
                Rule::field_decl => fields.push(self.build_field_decl(&mut pair.into_inner(), context)),
                rule => unreachable!("Rule {:?}", rule),
            }
        }
        let r#struct = StructDecl {
            name: name.clone(),
            fields,
            attributes
        };
        context.structs.insert(name, r#struct.clone());
        r#struct
    }

    fn build_macro_attribute(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> MacroKind {
        MacroKind::from(pairs)
    }

    fn build_import(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Import {
        let mut namespace = Namespace::default();
        for pair in pairs {
            match pair.as_rule() {
                Rule::namespace => namespace = self.build_namespace(&mut pair.into_inner()),
                _ => unreachable!(),
            }
        }
        Import { kind: ImportKind::Static, namespace }
    }

    fn build_namespace(&self, pairs: &mut Pairs<Rule>) -> Namespace {
        let mut name = String::new();
        let mut next = vec![];
        for pair in pairs {
            match pair.as_rule() {
                Rule::namespace_name => name = pair.as_str().into(),
                Rule::namespace => next.push(Box::new(self.build_namespace(&mut pair.into_inner()))),
                _ => unreachable!()
            }
        }
        Namespace { name, next }
    }

    fn build_single_value(&self, pair: &mut Pair<Rule>, context: &mut AstContext) -> Value {
        match pair.as_rule() {
            Rule::unary_operation | Rule::binary_operation => self.build_binary_op(&mut pair.clone().into_inner(), context),
            Rule::bvalue => self.build_bvalue(&mut pair.clone().into_inner(), context),
            Rule::base_value => self.build_base(&mut pair.clone().into_inner(), context),
            rule => unreachable!("Found rule {:?} while building single value", rule),
        }
    }

    fn build_overloaded(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Overloaded {
        let mut lhs = OverloadedLHS::Name(Name {
            name: String::new(),
            op: None,
            op_count: 0,
        });
        let mut op = OverloadedOp::Add;
        let mut rhs = Value::default();
        for mut pair in pairs {
            match pair.as_rule() {
                Rule::name => {
                    lhs = OverloadedLHS::Name(self.build_name(&mut pair.into_inner(), context))
                }
                Rule::field_access => {
                    lhs = OverloadedLHS::FieldAccess(
                        self.build_field_access(&mut pair.into_inner(), context),
                    )
                }
                Rule::overloaded_ops => {
                    op = self.build_overloaded_op(&mut pair.into_inner(), context)
                }
                Rule::bvalue
                | Rule::base_value
                | Rule::unary_operation
                | Rule::binary_operation => rhs = self.build_single_value(&mut pair, context),
                rule => unreachable!("Found rule {:?} while building overloaded op", rule),
            }
        }
        Overloaded { lhs, op, rhs }
    }

    fn build_overloaded_op(
        &self,
        pairs: &mut Pairs<Rule>,
        context: &mut AstContext,
    ) -> OverloadedOp {
        let eval = pairs.peek().unwrap();
        match eval.as_rule() {
            Rule::add_to => OverloadedOp::Add,
            Rule::sub_to => OverloadedOp::Sub,
            Rule::mul_to => OverloadedOp::Mul,
            Rule::div_to => OverloadedOp::Div,
            _ => unreachable!(),
        }
    }

    fn build_assignment(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Assignment {
        let mut var = AssignVar::Name(Name {
            name: String::new(),
            op: None,
            op_count: 0,
        });
        let mut value = Value::default();
        for mut pair in pairs {
            match pair.as_rule() {
                Rule::array_access => {
                    var =
                        AssignVar::Access(self.build_array_access(&mut pair.into_inner(), context))
                }
                Rule::name => {
                    var = AssignVar::Name(self.build_name(&mut pair.into_inner(), context))
                }
                Rule::field_access => {
                    var = AssignVar::FieldAccess(
                        self.build_field_access(&mut pair.into_inner(), context),
                    )
                }
                Rule::unary_operation
                | Rule::bvalue
                | Rule::base_value
                | Rule::binary_operation => value = self.build_single_value(&mut pair, context),
                rule => unreachable!("Found rule {:?} while building assignment", rule),
            }
        }
        Assignment { var, value }
    }

    fn build_operation(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Operation {
        let mut lhs = Value::default();
        let mut rhs = Value::default();
        let mut op = Operations::Add;
        let mut changed = false;
        for pair in pairs {
            match pair.as_rule() {
                Rule::add => op = Operations::Add,
                Rule::sub => op = Operations::Sub,
                Rule::mul => op = Operations::Mul,
                Rule::div => op = Operations::Div,
                Rule::and => op = Operations::And,
                Rule::or => op = Operations::Or,
                Rule::lt => op = Operations::Lt,
                Rule::gt => op = Operations::Gt,
                Rule::lte => op = Operations::Lte,
                Rule::gte => op = Operations::Gte,
                Rule::cmp_eq => op = Operations::Eq,
                Rule::neq => op = Operations::Neq,
                Rule::modulo => op = Operations::Modulo,
                _ => unreachable!("Infix wtf"),
            }
        }
        if !changed {
            Operation::BinaryOp(BinaryOp {
                lhs: Rc::new(RefCell::new(lhs)),
                op,
                rhs: Rc::new(RefCell::new(rhs)),
            })
        } else {
            Operation::UnaryOp(UnaryOp {
                value: Rc::new(RefCell::new(lhs)),
                prefix: op,
            })
        }
    }

    pub fn build_return(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Return {
        if let Some(mut pair) = pairs.next() {
            let value = self.build_single_value(&mut pair, context);
            Return { value: Some(value) }
        } else {
            Return { value: None }
        }
    }

    fn build_bvalue(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Value {
        let mut value = Value::default();
        for pair in pairs {
            match pair.as_rule() {
                Rule::base_value => value = self.build_base(&mut pair.into_inner(), context),
                Rule::type_casting => {
                    let eval = pair.into_inner().peek().unwrap();
                    value.value = ValueEnum::Casting((
                        Rc::new(RefCell::new(value.clone())),
                        self.build_datatype(&mut eval.into_inner(), context),
                    ))
                }
                rule => unreachable!("Found rule {:?} while building bvalue", rule),
            }
        }
        value
    }

    fn build_base(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Value {
        let mut value = Value::default();
        for mut eval in pairs {
            match eval.as_rule() {
                Rule::call => {
                    let call = self.build_call(&mut eval.into_inner(), context);
                    value.heap_allocated = call.name.name.as_str() == "malloc";
                    value.value = ValueEnum::Call(call);
                }
                Rule::name => {
                    value.value = ValueEnum::Name(self.build_name(&mut eval.into_inner(), context))
                }
                Rule::r#if => {
                    value.value = ValueEnum::If(self.build_if(&mut eval.into_inner(), context))
                }
                Rule::array => {
                    value.value =
                        ValueEnum::Array(self.build_array(&mut eval.into_inner(), context))
                }
                Rule::array_access => {
                    value.value = ValueEnum::ArrayAccess(Rc::new(RefCell::new(
                        self.build_array_access(&mut eval.into_inner(), context),
                    )))
                }
                Rule::constructor => {
                    value.value = ValueEnum::Constructor(Rc::new(RefCell::new(
                        self.build_constructor(&mut eval.into_inner(), context),
                    )));
                }
                Rule::field_access => {
                    value.value = ValueEnum::FieldAccess(Rc::new(RefCell::new(
                        self.build_field_access(&mut eval.into_inner(), context),
                    )));
                }
                Rule::string => value.value = self.build_string_value(eval, context),
                Rule::integer => value.value = self.build_integer(eval, context),
                Rule::float => value.value = self.build_float(eval, context),
                Rule::r#bool => value.value = self.build_bool(eval, context),
                Rule::char_value => value.value = self.build_char(eval, context),
                Rule::type_casting => {
                    let eval = eval.into_inner().peek().unwrap();
                    value.value = ValueEnum::Casting((
                        Rc::new(RefCell::new(value.clone())),
                        self.build_datatype(&mut eval.into_inner(), context),
                    ))
                }
                Rule::unary_operation
                | Rule::bvalue
                | Rule::base_value
                | Rule::binary_operation => value = self.build_single_value(&mut eval, context),
                Rule::range => {
                    value.value =
                        ValueEnum::Range(self.build_range(&mut eval.into_inner(), context))
                }
                Rule::enum_build => {
                    let mut datatype = String::new();
                    let mut variant = String::new();
                    let mut inner = None;
                    for mut rule in eval.into_inner() {
                        match rule.as_rule() {
                            Rule::struct_type => datatype = rule.as_str().into(),
                            Rule::enum_variant_name => variant = rule.as_str().into(),
                            Rule::base_value | Rule::unary_operation | Rule::binary_operation | Rule::bvalue => inner = Some(self.build_single_value(&mut rule, context)),
                            rule => unreachable!("Found rule {:?}", rule)
                        }
                    }
                    value.value = ValueEnum::Enum(Rc::new(RefCell::new(EnumValue { datatype, variant, inner })))
                }
                Rule::closure => {
                    value.value = ValueEnum::Closure(Rc::new(RefCell::new(self.build_closure(&mut eval.into_inner(), context))));
                }
                rule => unreachable!("Fucked up rule is {:?}", rule),
            };
        }
        value
    }

    fn build_closure(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Closure {
        let mut args = Vec::new();
        let mut block = Block::default();
        for pair in pairs {
            match pair.as_rule() {
                Rule::name_str => args.push(pair.as_str().to_string()),
                Rule::block => block = self.build_block(&mut pair.into_inner(), context),
                _ => unreachable!()
            }
        }
        Closure { args, block: Rc::new(RefCell::new(block)) }
    }

    fn build_binary_op(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Value {
        fn bop_helper(lhs: Value, op: Pair<'_, Rule>, rhs: Value) -> Value {
            Value::non_heap(ValueEnum::BinaryOp(Rc::new(RefCell::new(BinaryOp { lhs: Rc::new(RefCell::new(lhs)), op: Operations::from(op), rhs: Rc::new(RefCell::new(rhs)) }))))
        }
        fn unop_helper(value: Value, op: Pair<'_, Rule>) -> Value {
            Value::non_heap(ValueEnum::UnaryOp(Rc::new(RefCell::new(UnaryOp { prefix: Operations::from(op), value: Rc::new(RefCell::new(value)) }))))
        }

        self.pratt_parser.map_primary(|mut primary| match primary.as_rule() {
            Rule::bvalue | Rule::base_value | Rule::binary_operation => self.build_single_value(&mut primary, context),
            _ => unreachable!()
        }).map_infix(|lhs, op, rhs| bop_helper(lhs, op, rhs))
          .map_prefix(|op, value| unop_helper(value, op))
          .parse(pairs)
    }

    fn build_range(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> RangeValue {
        if pairs.len() > 1 {
            let mut start = Value::default();
            let mut end = Value::default();
            let mut range_type = RangeType::Exclusive;
            let mut changed = false;
            for pair in pairs {
                match pair.as_rule() {
                    Rule::bvalue => {
                        if changed {
                            end = self.build_bvalue(&mut pair.into_inner(), context);
                        } else {
                            start = self.build_bvalue(&mut pair.into_inner(), context);
                            changed = true;
                        }
                    }
                    Rule::range_type => {
                        range_type = self.build_range_type(&mut pair.into_inner(), context)
                    }
                    rule => unreachable!("Found rule {:?} while building range", rule),
                }
            }
            RangeValue::Range(Rc::new(RefCell::new(Range {
                start,
                range_type,
                end,
            })))
        } else {
            let value = pairs.peek().unwrap();
            RangeValue::Iterable(Rc::new(RefCell::new(match value.as_rule() {
                Rule::unary_operation | Rule::binary_operation => self.build_binary_op(&mut value.into_inner(), context),
                Rule::bvalue => self.build_bvalue(&mut value.into_inner(), context),
                Rule::base_value => self.build_base(&mut value.into_inner(), context),
                rule => unreachable!("Found rule {:?} while building iterable range", rule),
            })))
        }
    }

    fn build_range_type(&self, pairs: &mut Pairs<Rule>, _context: &mut AstContext) -> RangeType {
        let eval = pairs.peek().unwrap();
        match eval.as_rule() {
            Rule::range_exclusive => RangeType::Exclusive,
            Rule::range_inclusive => RangeType::Inclusive,
            _ => todo!(),
        }
    }

    fn build_field_access(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> FieldAccess {
        let mut head: FieldAccess = FieldAccess::default();
        let mut next = head.next.clone();
        let mut op_count = 0;
        let mut ref_op = None;
        let mut flag = false;

        for pair in pairs {
            let mut name = FieldAccessName::Name(Name::default());
            match pair.as_rule() {
                Rule::name => {
                    name = FieldAccessName::Name(self.build_name(&mut pair.into_inner(), context));
                }
                Rule::call => {
                    name = FieldAccessName::Call(self.build_call(&mut pair.into_inner(), context));
                }
                Rule::array_access => {
                    name = FieldAccessName::ArrayAccess(
                        self.build_array_access(&mut pair.into_inner(), context),
                    )
                }
                Rule::r#ref => {
                    ref_op = Some(RefOp::Reference);
                    op_count += 1;
                }
                Rule::deref => {
                    ref_op = Some(RefOp::Dereference);
                    op_count += 1;
                }
                rule => unreachable!("Found rule {:?}", rule),
            };
            let field_access = FieldAccess {
                name,
                next: Rc::new(RefCell::new(None)),
                op: ref_op.clone(),
                op_count,
            };
            if !flag {
                head = field_access;
                next = head.next.clone();
                flag = true;
            } else {
                next.swap(&Rc::new(RefCell::new(Some(field_access))));
                next = Rc::make_mut(&mut next)
                    .get_mut()
                    .as_mut()
                    .unwrap()
                    .next
                    .clone();
            }
        }
        head
    }

    fn build_constructor(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Constructor {
        let mut name = String::new();
        let mut fields = Vec::new();
        for pair in pairs {
            match pair.as_rule() {
                Rule::name_str => name = pair.as_str().into(),
                Rule::field => fields.push(self.build_field(&mut pair.into_inner(), context)),
                _ => unreachable!(),
            }
        }
        Constructor { name, fields }
    }

    fn build_field(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Field {
        let mut name = String::new();
        let mut value = Value::default();
        for pair in pairs {
            match pair.as_rule() {
                Rule::name_str => name = pair.as_str().into(),
                Rule::unary_operation | Rule::bvalue => value = self.build_bvalue(&mut pair.into_inner(), context),
                Rule::binary_operation => {
                    value = self.build_binary_op(&mut pair.into_inner(), context)
                }
                Rule::base_value => value = self.build_base(&mut pair.into_inner(), context),
                rule => unreachable!("Found rule {:?} while building field", rule),
            }
        }
        Field { name, value }
    }

    fn build_array_access(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> ArrayAccess {
        let mut value = Value::default();
        let mut index = Value::default();
        for pair in pairs {
            match pair.as_rule() {
                Rule::call => {
                    value.value = ValueEnum::Call(self.build_call(&mut pair.into_inner(), context))
                }
                Rule::unary_operation | Rule::binary_operation => {
                    index = self.build_binary_op(&mut pair.into_inner(), context)
                }
                Rule::bvalue => index = self.build_bvalue(&mut pair.into_inner(), context),
                Rule::name => {
                    value.value = ValueEnum::Name(self.build_name(&mut pair.into_inner(), context))
                }
                rule => unreachable!("Found rule {:?} while building array access", rule),
            }
        }
        ArrayAccess { value, index }
    }

    fn build_char(&self, pair: Pair<Rule>, context: &mut AstContext) -> ValueEnum {
        let aux = pair.as_str();
        let aux = &aux[1..aux.len() - 1];
        let aux = if aux.len() > 1 {
            match aux {
                "\\n" => '\n',
                "\\t" => '\t',
                "\\0" => '\0',
                "\\r" => '\r',
                seq => unreachable!("Found sequence {} {:?}", seq, seq.as_bytes())
            }
        }else{
            aux.chars().next().unwrap()
        };
        ValueEnum::Char(aux)
    }

    fn build_array(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Array {
        let mut datatype = ArrayType {
            size: Value::non_heap(ValueEnum::Int(0)),
            data_type: Type { is_ref: false, ref_count: 0, datatype: DataType::Int(4) },
        };
        let mut elements = Vec::new();
        for pair in pairs {
            match pair.as_rule() {
                Rule::array_type => datatype = self.build_array_type(&mut pair.into_inner(), context),
                Rule::bvalue | Rule::base_value | Rule::unary_op | Rule::binary_op => {
                    let element = self.build_binary_op(&mut pair.into_inner(), context);
                    elements.push(element);
                }
                rule => unreachable!("Found rule {:?} while building array", rule),
            }
        }
        datatype.size = Value::non_heap(ValueEnum::Int(elements.len() as i32));
        let datatype = Type { is_ref: false, ref_count: 0, datatype: DataType::Array(Rc::new(RefCell::new(datatype))) };
        Array { datatype, elements }
    }

    fn build_array_type(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> ArrayType {
        let mut size = Value::default();
        let mut data_type = Type::default();
        for pair in pairs {
            match pair.as_rule() {
                Rule::bvalue | Rule::base_value | Rule::unary_op | Rule::binary_op => size = self.build_binary_op(&mut pair.into_inner(), context),
                Rule::datatype => data_type = self.build_datatype(&mut pair.into_inner(), context),
                rule => unreachable!("Found {:?} while building array type", rule),
            }
        }
        ArrayType { size, data_type }
    }

    fn build_if(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> If {
        let mut value = If {
            not: false,
            condition: None,
            enum_match: None,
            block: Rc::new(RefCell::new(Block {
                expr: Vec::new(),
                box_return: None,
            })),
            otherwise: None,
        };
        for pair in pairs {
            match pair.as_rule() {
                Rule::not => value.not = true,
                Rule::binary_operation => {
                    value.condition = Some(Rc::new(RefCell::new(
                        self.build_binary_op(&mut pair.into_inner(), context),
                    )))
                }
                Rule::bvalue => {
                    value.condition = Some(Rc::new(RefCell::new(
                        self.build_bvalue(&mut pair.into_inner(), context),
                    )))
                }
                Rule::base_value => {
                    value.condition = Some(Rc::new(RefCell::new(
                        self.build_base(&mut pair.into_inner(), context),
                    )))
                }
                Rule::block => {
                    value.block = Rc::new(RefCell::new(
                        self.build_block(&mut pair.into_inner(), context),
                    ))
                }
                Rule::otherwise => {
                    value.otherwise = Some(Rc::new(RefCell::new(
                        self.build_otherwise(&mut pair.into_inner(), context),
                    )))
                }
                Rule::enum_match => {
                    let mut name = String::new();
                    let mut variant = String::new();
                    let mut var = String::new();
                    let mut switch = false;
                    for eval in pair.into_inner() {
                        match eval.as_rule() {
                            Rule::name_str => if !switch { switch = true; name = eval.as_str().into(); } else { var = eval.as_str().into(); },
                            Rule::enum_variant_name => variant = eval.as_str().into(),
                            _ => unreachable!()
                        }
                    }
                    value.enum_match = Some(EnumMatch { name, variant, var })
                }
                rule => unreachable!("Found rule {:?} while building if", rule),
            };
        }
        value
    }

    fn build_otherwise(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Otherwise {
        let eval = pairs.peek().unwrap();
        return match eval.as_rule() {
            Rule::r#if => Otherwise::If(self.build_if(&mut eval.into_inner(), context)),
            Rule::block => Otherwise::Block(self.build_block(&mut eval.into_inner(), context)),
            rule => unreachable!("{:?}", rule),
        };
    }

    fn build_bool(&self, pair: Pair<Rule>, context: &mut AstContext) -> ValueEnum {
        ValueEnum::Bool(pair.as_str().parse().unwrap())
    }

    fn build_call(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Call {
        let mut call = Call {
            neg: false,
            name: Name {
                name: String::new(),
                op: None,
                op_count: 0,
            },
            args: Vec::new(),
        };
        for pair in pairs {
            match pair.as_rule() {
                Rule::name => call.name = self.build_name(&mut pair.into_inner(), context),
                Rule::arg => call
                    .args
                    .push(self.build_single_value(&mut pair.into_inner().next().unwrap(), context)),
                rule => unreachable!("Found rule {:?}", rule),
            }
        }
        call
    }

    fn build_function(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Function {
        let mut function = Function {
            kind: FunctionKind::Native,
            name: Name {
                name: String::new(),
                op: None,
                op_count: 0,
            },
            args: Vec::new(),
            return_type: None,
            block: Rc::new(RefCell::new(Block {
                expr: Vec::new(),
                box_return: None,
            })),
        };
        let aux = context.scope.clone();
        for pair in pairs.clone() {
            match pair.as_rule() {
                Rule::function_kind => function.kind = self.build_function_kind(&pair, context),
                Rule::name => {
                    function.name = self.build_name(&mut pair.into_inner(), context);
                    context.scope = function.name.name.clone();
                }
                Rule::args => function.args = self.build_args(&mut pair.into_inner(), context),
                Rule::datatype => {
                    function.return_type =
                        Some(self.build_datatype(&mut pair.into_inner(), context))
                }
                Rule::block => {
                    function.block = Rc::new(RefCell::new(
                        self.build_block(&mut pair.into_inner(), context),
                    ))
                }
                _ => unreachable!(),
            }
        }
        context.scope = aux;
        context
            .functions
            .insert(function.name.name.clone(), function.clone());
        function
    }

    fn build_function_kind(&self, pair: &Pair<Rule>, context: &mut AstContext) -> FunctionKind {
        FunctionKind::from_str(pair.as_str())
    }


    fn build_block(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Block {
        let mut block = Block {
            expr: Vec::new(),
            box_return: None,
        };
        let expressions = self.build_expression(pairs, context);
        for expression in expressions {
            match expression {
                Expr::Return(r#return) => {

                    block.box_return = Some(r#return);
                }
                val => block.expr.push(Rc::new(RefCell::new(val))),
            }
        }
        block
    }

    fn build_declaration(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Declaration {
        let mut declaration = Declaration {
            name: Name {
                name: String::new(),
                op: None,
                op_count: 0,
            },
            datatype: None,
            value: None,
        };
        for mut pair in pairs {
            match pair.as_rule() {
                Rule::name => declaration.name = self.build_name(&mut pair.into_inner(), context),
                Rule::bvalue | Rule::base_value | Rule::binary_operation | Rule::unary_operation => {
                    declaration.value = Some(self.build_single_value(&mut pair, context))
                }
                Rule::datatype => {
                    declaration.datatype =
                        Some(self.build_datatype(&mut pair.into_inner(), context))
                }
                rule => unreachable!("Found rule {:?} while building declaration", rule),
            }
        }
        if let Some(ref value) = declaration.value {
            let binding = context
                .variables
                .entry(context.scope.clone())
                .or_insert(HashMap::new());
            binding.insert(declaration.name.name.clone(), value.clone());
        }
        declaration
    }

    fn build_string_value(&self, pair: Pair<Rule>, context: &mut AstContext) -> ValueEnum {
        let mut literal = Vec::<String>::with_capacity(pair.as_str().len());
        let iterator = pair.as_str().chars();
        let mut escaping = false;
        for c in iterator {
            let mut repr = c.to_string();
            if escaping {
                match c {
                    'n' => repr = "\n".to_string(),
                    'r' => repr = "\r".to_string(),
                    _ => (),
                };
                escaping = false;
                literal.push(repr);
            } else {
                match c {
                    '\\' => escaping = true,
                    _ => {
                        literal.push(repr);
                        escaping = false
                    }
                };
            }
        }
        ValueEnum::String(literal.concat())
    }

    fn build_integer(&self, pair: Pair<Rule>, context: &mut AstContext) -> ValueEnum {
        let clone = pair.clone();
        if clone.into_inner().peek().is_some() {
            return ValueEnum::UInt(pair.as_str()[1..].parse().unwrap());
        }
        ValueEnum::Int(pair.as_str().trim().parse().unwrap())
    }

    fn build_float(&self, pair: Pair<Rule>, context: &mut AstContext) -> ValueEnum {
        ValueEnum::Float(pair.as_str().parse().unwrap())
    }

    fn build_name(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Name {
        let mut name = String::new();
        let mut op = None;
        let mut op_count = 0;
        for pair in pairs {
            match pair.as_rule() {
                Rule::name_str => name = pair.as_str().trim().into(),
                Rule::r#ref => {
                    op = Some(RefOp::Reference);
                    op_count += 1;
                }
                Rule::deref => {
                    op = Some(RefOp::Dereference);
                    op_count += 1;
                }
                _ => unreachable!(),
            }
        }
        Name { name, op, op_count }
    }

    fn build_param(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Parameter {
        let pair = pairs.next().unwrap();
        match pair.as_rule() {
            Rule::name => Parameter::Name(self.build_name(&mut pair.into_inner(), context)),
            Rule::binary_op => {
                Parameter::Value(self.build_binary_op(&mut pair.into_inner(), context))
            }
            rule => unreachable!("Found rule {:?} while building param", rule),
        }
    }

    fn build_args(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Vec<Arg> {
        let mut args = Vec::new();
        for pair in pairs {
            match pair.as_rule() {
                Rule::parameter => args.push(self.build_arg(&mut pair.into_inner(), context)),
                rule => unreachable!("{:?}", rule),
            }
        }
        args
    }

    fn build_arg(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Arg {
        let mut arg = Arg {
            name: Name {
                name: String::new(),
                op: None,
                op_count: 0,
            },
            datatype: ParameterType::Type(Type::default()),
        };
        for pair in pairs {
            match pair.as_rule() {
                Rule::name => arg.name = self.build_name(&mut pair.into_inner(), context),
                Rule::datatype => {
                    arg.datatype = ParameterType::Type(self.build_datatype(&mut pair.into_inner(), context))
                }
                Rule::implements_type => arg.datatype = ParameterType::Implements(self.build_implements_type(&mut pair.into_inner(), context)),
                _ => unreachable!(),
            }
        }
        arg
    }

    fn build_implements_type(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Vec<String> {
        pairs.map(|x| if let Rule::name_str = x.as_rule() { x.as_str().to_string() } else { panic!() }).collect()
    }

    fn build_datatype(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Type {
        let mut is_ref = false;
        let mut ref_count = 0;
        let mut datatype = DataType::Int(0);
        for pair in pairs {
            match pair.as_rule() {
                Rule::float_type => {
                    datatype = self.build_float_type(&mut pair.into_inner(), context)
                }
                Rule::int_type => datatype = self.build_int_type(&mut pair.into_inner(), context),
                Rule::r#struct => {
                    datatype = DataType::Struct(Rc::new(RefCell::new(
                        self.build_struct(&mut pair.into_inner(), context),
                    )))
                }
                Rule::array_type => {
                    datatype = DataType::Array(Rc::new(RefCell::new(
                        self.build_array_type(&mut pair.into_inner(), context),
                    )))
                }
                Rule::struct_type => {
                    datatype = DataType::StructType(
                        self.build_struct_type(&pair, context),
                    )
                }
                Rule::string_type => datatype = DataType::String,
                Rule::char_type => datatype = DataType::Char,
                Rule::bool_type => datatype = DataType::Bool,
                Rule::trait_type => datatype = DataType::Trait(pair.as_str()[1..].into()),
                Rule::any_type => datatype = DataType::Any,
                Rule::r#ref => {
                    is_ref = true;
                    ref_count += 1;
                }
                rule => unreachable!("Got rule {:?}", rule),
            };
        }
        Type {
            is_ref,
            ref_count,
            datatype,
        }
    }

    fn build_struct_type(&self, pair: &Pair<Rule>, context: &mut AstContext) -> String {
        pair.as_str().into()
    }

    fn build_int_type(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> DataType {
        let mut bytecount = 4;
        let mut is_unsigned = false;
        for pair in pairs {
            match pair.as_rule() {
                Rule::integer => bytecount = pair.as_str().trim().parse().unwrap(),
                Rule::unsigned => is_unsigned = true,
                _ => unreachable!(),
            }
        }
        if is_unsigned {
            return DataType::UInt(bytecount);
        }
        DataType::Int(bytecount)
    }

    fn build_float_type(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> DataType {
        let mut bytecount = 4;
        for pair in pairs {
            match pair.as_rule() {
                Rule::integer => bytecount = pair.as_str().parse().unwrap(),
                _ => unreachable!(),
            }
        }
        DataType::Float(bytecount)
    }
}
