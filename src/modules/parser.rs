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
    pub imports: HashMap<Import, Rc<RefCell<Ast>>>,
    pub context: AstContext,
}

pub struct NoirParser {
    pub pratt_parser: PrattParser<Rule>,
}

impl NoirParser {
    pub fn new() -> Self {
        let pratt_parser = PrattParser::new()
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
            .op(Op::prefix(Rule::unary_minus) | Op::prefix(Rule::not));
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
        }
    }

    fn load_imports(
        &self,
        imports: &Vec<Import>,
        context: &mut AstContext,
    ) -> HashMap<Import, Rc<RefCell<Ast>>> {
        let mut rtn = HashMap::new();
        for import in imports {
            let lib_path = self.parse_import_path(&import);
            let lib_path = format!("{}.apo", lib_path);
            println!("{lib_path}");
            let input = std::fs::read_to_string(lib_path).unwrap();
            let mut pairs: Pairs<Rule> = Program::parse(Rule::program, &input).unwrap();
            let ast = self.gen_ast(&mut pairs, import.name.clone());
            rtn.insert(import.clone(), Rc::new(RefCell::new(ast)));
        }
        rtn
    }

    fn parse_import_path(&self, import: &Import) -> String {
        let names = import.name.split("::").collect::<Vec<_>>();
        let mut final_path = Vec::new();
        final_path.push(match names[0] {
            "std" => std::env::var("APOLLO_LIBS").unwrap(),
            _ => format!(
                "{}/{}",
                std::env::current_dir().unwrap().to_str().unwrap(),
                names[0]
            ),
        });
        for i in 1..names.len() {
            final_path.push(names[i].to_string());
        }
        final_path.join("/")
    }

    fn build_expression(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Vec<Expr> {
        let mut expressions = Vec::new();

        for pair in pairs {
            let expr = match pair.as_rule() {
                Rule::r#return => Expr::Return(self.build_return(&mut pair.into_inner(), context)),
                Rule::call => Expr::Call(self.build_call(&mut pair.into_inner(), context)),
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
                Rule::EOI => continue,
                rule => unreachable!("{:?}", rule),
            };
            expressions.push(expr);
        }
        context.variables.iter().for_each(|(_, y)| {
            y.iter().for_each(|(x, y)| {
                if y.heap_allocated {
                    println!("{} is heap allocated", x)
                } else {
                    println!("{} is stack allocated. value set to {:?}", x, y)
                }
            })
        });
        expressions
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
        Enum {
            name, variants
        }
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
        let mut struct_name = String::new();
        let mut block = Block::default();
        for pair in pairs {
            match pair.as_rule() {
                Rule::name => {
                    if switched {
                        struct_name = pair.as_str().into();
                    } else {
                        trait_name = pair.as_str().into();
                        switched = true;
                    }
                }
                Rule::impl_block => block = self.build_block(&mut pair.into_inner(), context),
                _ => todo!(),
            }
        }
        Impl {
            trait_name,
            struct_name,
            block,
        }
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
        let mut fields = Vec::new();
        for pair in pairs {
            match pair.as_rule() {
                Rule::name_str => name = pair.as_str().into(),
                Rule::field_decl => {
                    fields.push(self.build_field_decl(&mut pair.into_inner(), context))
                }
                _ => unreachable!(),
            }
        }
        Trait { name, fields }
    }

    fn build_struct(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> StructDecl {
        let mut name = String::new();
        let mut fields = Vec::new();
        let mut traits = Vec::new();
        for pair in pairs {
            match pair.as_rule() {
                Rule::name_str => name = pair.as_str().into(),
                Rule::field_decl => {
                    fields.push(self.build_field_decl(&mut pair.into_inner(), context))
                }
                Rule::trait_field => traits.push(pair.as_str()[2..pair.as_str().len() - 1].into()),
                rule => unreachable!("Rule {:?}", rule),
            }
        }
        let r#struct = StructDecl {
            name: name.clone(),
            fields,
            traits,
        };
        context.structs.insert(name, r#struct.clone());
        r#struct
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

    fn build_import(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Import {
        let mut import = Import {
            kind: ImportKind::Static,
            name: String::new(),
            imported: Vec::new(),
        };
        for pair in pairs {
            match pair.as_rule() {
                Rule::namespace => import.name = self.build_namespace(&mut pair.into_inner()),
                _ => unreachable!(),
            }
        }
        context.imported.push(import.clone());
        import
    }

    fn build_imported_fn(&self, pairs: &mut Pairs<Rule>) -> Vec<String> {
        let mut imports = Vec::new();
        for pair in pairs {
            let eval = pair
                .into_inner()
                .map(|x| x.as_str().to_string())
                .collect::<Vec<_>>();
            imports.push(eval.join("/"));
        }
        imports
    }

    fn build_namespace(&self, pairs: &mut Pairs<Rule>) -> String {
        let mut vec = Vec::new();
        for pair in pairs {
            vec.push(pair.as_str().to_string());
        }
        vec.join("::")
    }

    fn build_single_value(&self, pair: &mut Pair<Rule>, context: &mut AstContext) -> Value {
        match pair.as_rule() {
            Rule::binary_operation => self.build_binary_op(&mut pair.clone().into_inner(), context),
            Rule::unary_operation => self.build_unary_op(&mut pair.clone().into_inner(), context),
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
                Rule::unary_minus => op = Operations::Sub,
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
        if let Some(pair) = pairs.next() {
            let value = self.build_value(&mut pair.into_inner(), context);
            Return { value: Some(value) }
        } else {
            Return { value: None }
        }
    }

    fn build_unary_op(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Value {
        let mut op = Operations::Neg;
        let mut value = Value::default();
        for pair in pairs {
            match pair.as_rule() {
                Rule::unary_minus => op = Operations::Neg,
                Rule::not => op = Operations::Not,
                Rule::bvalue => value = self.build_bvalue(&mut pair.into_inner(), context),
                rule => unreachable!("Found rule {:?} while building unary operation", rule),
            }
        }
        let mut rtn = Value::default();
        rtn.value = ValueEnum::UnaryOp(Rc::new(RefCell::new(UnaryOp {
            prefix: op,
            value: Rc::new(RefCell::new(value)),
        })));
        rtn
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
                    println!("processed {:?}", value.value);
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
                    let mut switch = false;
                    for rule in eval.into_inner() {
                        match rule.as_rule() {
                            Rule::struct_type => if !switch { switch = true; datatype = rule.as_str().into(); } else { variant = rule.as_str().into(); },
                            Rule::bvalue => inner = Some(self.build_bvalue(&mut rule.into_inner(), context)),
                            Rule::value => inner = Some(self.build_value(&mut rule.into_inner(), context)),
                            Rule::binary_operation => inner = Some(self.build_binary_op(&mut rule.into_inner(), context)),
                            rule => unreachable!("Found rule {:?}", rule)
                        }
                    }
                    value.value = ValueEnum::Enum(Rc::new(RefCell::new(EnumValue { datatype, variant, inner })))
                }
                rule => unreachable!("Fucked up rule is {:?}", rule),
            };
        }
        value
    }

    fn build_binary_op(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Value {
        let mut lhs = Value::default();
        let mut rhs = Value::default();
        let mut changed = false;
        let mut op = Operations::Add;
        for pair in pairs {
            match pair.as_rule() {
                Rule::bvalue => {
                    let value = self.build_bvalue(&mut pair.into_inner(), context);
                    if changed {
                        rhs = value;
                    } else {
                        lhs = value;
                        changed = true
                    }
                }
                Rule::unary_minus => op = Operations::Sub,
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
                _ => todo!(),
            };
        }
        let mut rtn = Value::default();
        rtn.value = ValueEnum::BinaryOp(Rc::new(RefCell::new(BinaryOp {
            lhs: Rc::new(RefCell::new(lhs)),
            op,
            rhs: Rc::new(RefCell::new(rhs)),
        })));
        rtn
    }

    fn build_value(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Value {
        let mut peekable = pairs.peekable();
        let pair = peekable.peek().unwrap();
        match pair.as_rule() {
            Rule::binary_operation => self.build_binary_op(&mut pair.clone().into_inner(), context),
            Rule::unary_op => self.build_unary_op(&mut pair.clone().into_inner(), context),
            Rule::bvalue => self.build_bvalue(&mut pair.clone().into_inner(), context),
            Rule::base_value => self.build_base(&mut pair.clone().into_inner(), context),
            rule => unreachable!("Found rule {:?} while building value", rule),
        }
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
                Rule::binary_operation => self.build_binary_op(&mut value.into_inner(), context),
                Rule::bvalue => self.build_bvalue(&mut value.into_inner(), context),
                Rule::base_value => self.build_base(&mut value.into_inner(), context),
                Rule::unary_operation => self.build_unary_op(&mut value.into_inner(), context),
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
        println!("{:?}", head);
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
                Rule::unary_operation => {
                    value = self.build_unary_op(&mut pair.into_inner(), context)
                }
                Rule::bvalue => value = self.build_bvalue(&mut pair.into_inner(), context),
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
                Rule::binary_operation => {
                    index = self.build_binary_op(&mut pair.into_inner(), context)
                }
                Rule::unary_op => index = self.build_unary_op(&mut pair.into_inner(), context),
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
        ValueEnum::Char(*aux.chars().peekable().peek().unwrap())
    }

    fn build_array(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Array {
        let mut datatype = Type {
            is_ref: false,
            ref_count: 0,
            datatype: DataType::Int(4),
        };
        let mut elements = Vec::new();
        for pair in pairs {
            match pair.as_rule() {
                Rule::datatype => datatype = self.build_datatype(&mut pair.into_inner(), context),
                Rule::binary_op => {
                    let element = self.build_binary_op(&mut pair.into_inner(), context);
                    elements.push(element);
                }
                rule => unreachable!("Found rule {:?} while building array", rule),
            }
        }
        Array { datatype, elements }
    }

    fn build_array_type(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> ArrayType {
        let mut size = Value::default();
        let mut data_type = Type::default();
        for pair in pairs {
            match pair.as_rule() {
                Rule::binary_op => size = self.build_binary_op(&mut pair.into_inner(), context),
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
                            Rule::struct_type => variant = eval.as_str().into(),
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
                    .push(self.build_value(&mut pair.into_inner(), context)),
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

    fn is_struct_heap_allocated(
        &self,
        constructor: &mut Rc<RefCell<Constructor>>,
        context: &mut AstContext,
    ) -> bool {
        for field in Rc::get_mut(constructor).unwrap().get_mut().fields.iter() {
            if field.value.heap_allocated {
                return true;
            }
        }
        false
    }

    fn is_variable_heap_allocated(&self, name: &Name, context: &mut AstContext) -> bool {
        let binding = context.variables.get_mut(&context.scope).unwrap();
        if let Some(value) = binding.get(&name.name) {
            return value.heap_allocated;
        }
        false
    }

    fn is_operation_heap_allocated(
        &self,
        operation: &mut Rc<RefCell<Operation>>,
        context: &mut AstContext,
    ) -> bool {
        match Rc::get_mut(operation).unwrap().get_mut() {
            Operation::UnaryOp(ref mut op) => {
                Rc::get_mut(&mut op.value).unwrap().get_mut().heap_allocated
            }
            _ => false,
        }
    }

    fn build_block(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Block {
        let mut block = Block {
            expr: Vec::new(),
            box_return: None,
        };
        let expressions = self.build_expression(pairs, context);
        for expression in expressions {
            match expression {
                Expr::Return(mut r#return) => {
                    if let Some(ref mut val) = r#return.value {
                        match val.value {
                            ValueEnum::Array(_) | ValueEnum::String(_) => val.heap_allocated = true,
                            ValueEnum::Constructor(ref mut cons) => {
                                val.heap_allocated = self.is_struct_heap_allocated(cons, context)
                            }
                            ValueEnum::Name(ref name) => {
                                val.heap_allocated = self.is_variable_heap_allocated(name, context)
                            }
                            _ => (),
                        };
                    }
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
        for pair in pairs {
            match pair.as_rule() {
                Rule::name => declaration.name = self.build_name(&mut pair.into_inner(), context),
                Rule::binary_operation => {
                    declaration.value = Some(self.build_binary_op(&mut pair.into_inner(), context))
                }
                Rule::bvalue => {
                    declaration.value = Some(self.build_bvalue(&mut pair.into_inner(), context))
                }
                Rule::base_value => {
                    declaration.value = Some(self.build_base(&mut pair.into_inner(), context))
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
            datatype: Type::default(),
        };
        for pair in pairs {
            match pair.as_rule() {
                Rule::name => arg.name = self.build_name(&mut pair.into_inner(), context),
                Rule::datatype => {
                    arg.datatype = self.build_datatype(&mut pair.into_inner(), context)
                }
                _ => unreachable!(),
            }
        }
        arg
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
