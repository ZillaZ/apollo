use super::super::Program;
use super::ast_context::AstContext;
use crate::{modules::structs::*, Rule};
use pest::Parser;
use pest::{
    iterators::{Pair, Pairs},
    pratt_parser::{Assoc, Op, PrattParser},
};
use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct Ast {
    pub namespace: String,
    pub expressions: Vec<Expr>,
    pub imports: HashMap<Import, Box<Ast>>,
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
    ) -> HashMap<Import, Box<Ast>> {
        let mut rtn = HashMap::new();
        for import in imports {
            let lib_path = self.parse_import_path(&import);
            let lib_path = format!("{}.apo", lib_path);
            println!("{lib_path}");
            let input = std::fs::read_to_string(lib_path).unwrap();
            let mut pairs: Pairs<Rule> = Program::parse(Rule::program, &input).unwrap();
            let ast = self.gen_ast(&mut pairs, import.name.clone());
            rtn.insert(import.clone(), Box::new(ast));
        }
        rtn
    }

    fn parse_import_path(&self, import: &Import) -> String {
        let names = import.name.split("::").collect::<Vec<_>>();
        let mut final_path = Vec::new();
        final_path.push(match names[0] {
            "std" => std::env::var("APOLLO_LIBS").unwrap(),
            _ => std::env::current_dir().unwrap().to_str().unwrap().into(),
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
                Rule::compiler_extension => Expr::Extension(self.build_extension(&mut pair.into_inner(), context)),
                Rule::lib_link => Expr::Link(self.build_link(&mut pair.into_inner())),
                Rule::EOI => continue,
                rule => unreachable!("{:?}", rule),
            };
            expressions.push(expr);
        }

        expressions
    }

    fn build_link(&self, pairs: &mut Pairs<Rule>) -> LibLink {
        let mut eval = pairs.peekable();
        let eval = eval.peek().unwrap();
        LibLink {
            lib_name: eval.as_str().trim().into()
        }
    }

    fn build_extension(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Extension {
        let mut rtn = Extension {
            name: String::new(),
            body: String::new(),
        };
        for pair in pairs {
            match pair.as_rule() {
                Rule::name_str => rtn.name = pair.as_str().into(),
                Rule::string_value => rtn.body = pair.as_str().into(),
                _ => unreachable!()
            }
        }
        rtn
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
                Rule::r#static => import.kind = ImportKind::Static,
                Rule::r#dyn => import.kind = ImportKind::Dynamic,
                Rule::namespace => import.name = self.build_namespace(&mut pair.into_inner()),
                Rule::imported_fn => {
                    import.imported = self.build_imported_fn(&mut pair.into_inner())
                }
                _ => unreachable!(),
            }
        }
        context.imported.push(import.clone());
        import
    }

    fn build_imported_fn(&self, pairs: &mut Pairs<Rule>) -> Vec<String> {
        let mut imports = Vec::new();
        for pair in pairs {
            let eval = pair.into_inner().map(|x| x.as_str().to_string()).collect::<Vec<_>>();
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

    fn build_overloaded(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Overloaded {
        let mut lhs = OverloadedLHS::Name(Name {
            name: String::new(),
            op: None,
        });
        let mut op = OverloadedOp::Add;
        let mut rhs = Value::Int(0);
        for pair in pairs {
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
                Rule::value => rhs = self.build_value(&mut pair.into_inner(), context),
                _ => unreachable!(),
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
        });
        let mut value = Value::Int(0);
        for pair in pairs {
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
                Rule::value => value = self.build_value(&mut pair.into_inner(), context),
                _ => unreachable!(),
            }
        }
        Assignment { var, value }
    }

    fn build_operation(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Operation {
        self.pratt_parser
            .map_primary(|primary| match primary.as_rule() {
                Rule::atom => Operation::Atom(self.build_atom(&mut primary.into_inner(), context)),
                Rule::operation => self.build_operation(&mut primary.into_inner(), context),
                rule => unreachable!("Rule {:?}", rule),
            })
            .map_infix(|lhs, infix, rhs| {
                let op = match infix.as_rule() {
                    Rule::add => Operations::Add,
                    Rule::sub => Operations::Sub,
                    Rule::mul => Operations::Mul,
                    Rule::div => Operations::Div,
                    Rule::and => Operations::And,
                    Rule::or => Operations::Or,
                    Rule::lt => Operations::Lt,
                    Rule::gt => Operations::Gt,
                    Rule::lte => Operations::Lte,
                    Rule::gte => Operations::Gte,
                    Rule::cmp_eq => Operations::Eq,
                    Rule::neq => Operations::Neq,
                    Rule::modulo => Operations::Modulo,
                    _ => unreachable!("Infix wtf"),
                };
                Operation::BinaryOp(BinaryOp {
                    lhs: Box::new(lhs),
                    op,
                    rhs: Box::new(rhs),
                })
            })
            .map_prefix(|prefix, value| {
                let prefix = match prefix.as_rule() {
                    Rule::unary_minus => Operations::Neg,
                    Rule::not => Operations::Not,
                    rule => unreachable!("Prefix {:?}", rule),
                };
                Operation::UnaryOp(UnaryOp {
                    prefix,
                    value: Box::new(value),
                })
            })
            .parse(pairs)
    }

    pub fn build_return(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Return {
        if let Some(pair) = pairs.next() {
            let value = self.build_value(&mut pair.into_inner(), context);
            Return { value: Some(value) }
        } else {
            Return { value: None }
        }
    }

    fn build_value(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Value {
        let mut value = Value::Int(0);
        for eval in pairs {
            match eval.as_rule() {
                Rule::operation => {
                    value = Value::Operation(Box::new(
                        self.build_operation(&mut eval.into_inner(), context),
                    ))
                }
                Rule::call => value = Value::Call(self.build_call(&mut eval.into_inner(), context)),
                Rule::block => {
                    value =
                        Value::Block(Box::new(self.build_block(&mut eval.into_inner(), context)))
                }
                Rule::name => value = Value::Name(self.build_name(&mut eval.into_inner(), context)),
                Rule::atom => {
                    value = Value::Atom(Box::new(self.build_atom(&mut eval.into_inner(), context)))
                }
                Rule::r#if => value = Value::If(self.build_if(&mut eval.into_inner(), context)),
                Rule::array => {
                    value = Value::Array(self.build_array(&mut eval.into_inner(), context))
                }
                Rule::array_access => {
                    value = Value::ArrayAccess(Box::new(
                        self.build_array_access(&mut eval.into_inner(), context),
                    ))
                }
                Rule::constructor => {
                    value = Value::Constructor(Box::new(
                        self.build_constructor(&mut eval.into_inner(), context),
                    ))
                }
                Rule::field_access => {
                    value = Value::FieldAccess(Box::new(
                        self.build_field_access(&mut eval.into_inner(), context),
                    ))
                }
                Rule::string_value => value = self.build_string_value(eval, context),
                Rule::integer => value = self.build_integer(eval, context),
                Rule::float => value = self.build_float(eval, context),
                Rule::r#bool => value = self.build_bool(eval, context),
                Rule::r#char => value = self.build_char(eval, context),
                Rule::type_casting => {
                    value = Value::Casting((Box::new(value), eval.as_str()[3..].into()))
                }
                rule => unreachable!("{:?}", rule),
            };
        }
        value
    }
    fn build_field_access(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> FieldAccess {
        let mut head: Option<Box<FieldAccess>> = None;
        let mut prev = &mut head;

        for pair in pairs {
            let name = match pair.as_rule() {
                Rule::name => {
                    FieldAccessName::Name(self.build_name(&mut pair.into_inner(), context))
                }
                Rule::call => {
                    FieldAccessName::Call(self.build_call(&mut pair.into_inner(), context))
                }
                Rule::array_access => FieldAccessName::ArrayAccess(
                    self.build_array_access(&mut pair.into_inner(), context),
                ),
                rule => unreachable!("Found rule {:?}", rule),
            };
            let next = Box::new(FieldAccess { name, next: None });
            prev.replace(next.clone());
            prev = &mut prev.as_mut().expect("prev is sus").next;
        }

        *head.unwrap_or_else(|| {
            Box::new(FieldAccess {
                name: FieldAccessName::Name(Name {
                    name: String::new(),
                    op: None,
                }),
                next: None,
            })
        })
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
        let mut value = Parameter::Value(Value::Int(0));
        for pair in pairs {
            match pair.as_rule() {
                Rule::name_str => name = pair.as_str().into(),
                Rule::param => value = self.build_param(&mut pair.into_inner(), context),
                _ => unreachable!(),
            }
        }
        Field { name, value }
    }

    fn build_array_access(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> ArrayAccess {
        let mut value = Value::Int(0);
        let mut index = Value::Int(0);
        for pair in pairs {
            match pair.as_rule() {
                Rule::call => value = Value::Call(self.build_call(&mut pair.into_inner(), context)),
                Rule::value => index = self.build_value(&mut pair.into_inner(), context),
                Rule::name => value = Value::Name(self.build_name(&mut pair.into_inner(), context)),
                _ => unreachable!(),
            }
        }
        ArrayAccess { value, index }
    }

    fn build_char(&self, pair: Pair<Rule>, context: &mut AstContext) -> Value {
        let aux = pair.as_str();
        let aux = &aux[1..aux.len() - 1];
        Value::Char(*aux.chars().peekable().peek().unwrap())
    }

    fn build_array(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Array {
        let mut array_type = ArrayType {
            size: Value::Int(0),
            data_type: Type::default(),
        };
        let mut elements = Vec::new();
        for pair in pairs {
            match pair.as_rule() {
                Rule::array_type => {
                    array_type = self.build_array_type(&mut pair.into_inner(), context)
                }
                Rule::value => {
                    let element = self.build_value(&mut pair.into_inner(), context);
                    elements.push(element);
                }
                _ => unreachable!(),
            }
        }
        if array_type.size == Value::Int(0) {
            array_type.size = Value::Int(elements.len() as i32)
        }
        Array {
            array_type: Box::new(array_type),
            elements,
        }
    }

    fn build_array_type(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> ArrayType {
        let mut size = Value::Int(0);
        let mut data_type = Type::default();
        for pair in pairs {
            match pair.as_rule() {
                Rule::value => size = self.build_value(&mut pair.into_inner(), context),
                Rule::datatype => data_type = self.build_datatype(&mut pair.into_inner(), context),
                rule => unreachable!("{:?}", rule),
            }
        }
        ArrayType { size, data_type }
    }

    fn build_if(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> If {
        let mut value = If {
            not: false,
            condition: Box::new(Operation::Atom(Atom {
                is_neg: false,
                value: Value::Int(0),
            })),
            block: Box::new(Block {
                expr: Vec::new(),
                box_return: None,
            }),
            otherwise: None,
        };
        for pair in pairs {
            match pair.as_rule() {
                Rule::not => value.not = true,
                Rule::operation => {
                    value.condition =
                        Box::new(self.build_operation(&mut pair.into_inner(), context))
                }
                Rule::block => {
                    value.block = Box::new(self.build_block(&mut pair.into_inner(), context))
                }
                Rule::otherwise => {
                    value.otherwise =
                        Box::new(self.build_otherwise(&mut pair.into_inner(), context)).into()
                }
                rule => unreachable!("{:?}", rule),
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

    fn build_bool(&self, pair: Pair<Rule>, context: &mut AstContext) -> Value {
        Value::Bool(pair.as_str().parse().unwrap())
    }

    fn build_call(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Call {
        let mut call = Call {
            name: Name {
                name: String::new(),
                op: None,
            },
            args: Vec::new(),
        };
        for eval in pairs {
            match eval.as_rule() {
                Rule::name => call.name = self.build_name(&mut eval.into_inner(), context),
                Rule::param => call
                    .args
                    .push(self.build_param(&mut eval.into_inner(), context)),
                Rule::v => continue,
                _ => unreachable!(),
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
            },
            args: Vec::new(),
            return_type: None,
            block: Box::new(Block {
                expr: Vec::new(),
                box_return: None,
            }),
        };
        for pair in pairs.clone() {
            match pair.as_rule() {
                Rule::function_kind => function.kind = self.build_function_kind(&pair, context),
                Rule::name => function.name = self.build_name(&mut pair.into_inner(), context),
                Rule::args => function.args = self.build_args(&mut pair.into_inner(), context),
                Rule::datatype => {
                    function.return_type =
                        Some(self.build_datatype(&mut pair.into_inner(), context))
                }
                Rule::block => {
                    function.block = Box::new(self.build_block(&mut pair.into_inner(), context))
                }
                _ => unreachable!(),
            }
        }
        context
            .functions
            .insert(function.name.name.clone(), function.clone());
        function
    }

    fn build_function_kind(&self, pair: &Pair<Rule>, context: &mut AstContext) -> FunctionKind {
        FunctionKind::from_str(pair.as_str())
    }

    fn build_atom(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Atom {
        let mut atom = Atom {
            is_neg: false,
            value: Value::Int(0),
        };
        for pair in pairs {
            match pair.as_rule() {
                Rule::unary_minus => atom.is_neg = true,
                Rule::primary => atom.value = self.build_value(&mut pair.into_inner(), context),
                _ => unreachable!(),
            };
        }
        atom
    }

    fn build_block(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Block {
        let mut block = Block {
            expr: Vec::new(),
            box_return: None,
        };
        let expressions = self.build_expression(pairs, context);
        for expression in expressions {
            match expression {
                Expr::Return(r#return) => block.box_return = Some(r#return),
                val => block.expr.push(Box::new(val)),
            }
        }
        block
    }

    fn build_declaration(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Declaration {
        let mut declaration = Declaration {
            name: Name {
                name: String::new(),
                op: None,
            },
            datatype: None,
            value: Value::Int(0),
        };
        for pair in pairs {
            match pair.as_rule() {
                Rule::name => declaration.name = self.build_name(&mut pair.into_inner(), context),
                Rule::value => {
                    declaration.value = self.build_value(&mut pair.into_inner(), context)
                }
                Rule::datatype => {
                    declaration.datatype =
                        Some(self.build_datatype(&mut pair.into_inner(), context))
                }
                _ => unreachable!(),
            }
        }
        declaration
    }

    fn build_string_value(&self, pair: Pair<Rule>, context: &mut AstContext) -> Value {
        let mut literal = Vec::<String>::with_capacity(pair.as_str().len());
        let iterator = pair.as_str().chars();
        let mut escaping = false;
        for c in iterator {
            let mut repr = c.to_string();
            if escaping {
                match c {
                    'n' => repr = "\n".to_string(),
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
        Value::String(literal.concat())
    }

    fn build_integer(&self, pair: Pair<Rule>, context: &mut AstContext) -> Value {
        Value::Int(pair.as_str().parse().unwrap())
    }

    fn build_float(&self, pair: Pair<Rule>, context: &mut AstContext) -> Value {
        Value::Float(pair.as_str().parse().unwrap())
    }

    fn build_name(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Name {
        let mut name = String::new();
        let mut op = None;
        for pair in pairs {
            match pair.as_rule() {
                Rule::name_str => name = pair.as_str().trim().into(),
                Rule::r#ref => op = Some(RefOp::Reference),
                Rule::deref => op = Some(RefOp::Dereference),
                _ => unreachable!(),
            }
        }
        Name { name, op }
    }

    fn build_param(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Parameter {
        let pair = pairs.next().unwrap();
        match pair.as_rule() {
            Rule::name => Parameter::Name(self.build_name(&mut pair.into_inner(), context)),
            Rule::value => Parameter::Value(self.build_value(&mut pair.into_inner(), context)),
            _ => unreachable!(),
        }
    }

    fn build_args(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Vec<Arg> {
        let mut args = Vec::new();
        let mut arg = Arg {
            name: Name {
                name: String::new(),
                op: None,
            },
            datatype: Type::default(),
        };
        for pair in pairs {
            match pair.as_rule() {
                Rule::v => args.push(arg.clone()),
                Rule::name => arg.name = self.build_name(&mut pair.into_inner(), context),
                Rule::datatype => {
                    arg.datatype = self.build_datatype(&mut pair.into_inner(), context)
                }
                rule => unreachable!("{:?}", rule),
            }
        }
        args.push(arg.clone());
        args
    }

    fn build_datatype(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> Type {
        let mut is_ref = false;
        let mut datatype = DataType::Int(0);
        for pair in pairs {
            match pair.as_rule() {
                Rule::float_type => {
                    datatype = self.build_float_type(&mut pair.into_inner(), context)
                }
                Rule::int_type => datatype = self.build_int_type(&mut pair.into_inner(), context),
                Rule::r#struct => {
                    datatype = DataType::Struct(Box::new(
                        self.build_struct(&mut pair.into_inner(), context),
                    ))
                }
                Rule::array_type => {
                    datatype = DataType::Array(Box::new(
                        self.build_array_type(&mut pair.into_inner(), context),
                    ))
                }
                Rule::struct_type => {
                    datatype = DataType::StructType(
                        self.build_struct_type(&mut pair.into_inner(), context),
                    )
                }
                Rule::string_type => datatype = DataType::String,
                Rule::char_type => datatype = DataType::Char,
                Rule::bool_type => datatype = DataType::Bool,
                Rule::trait_type => datatype = DataType::Trait(pair.as_str()[1..].into()),
                Rule::any_type => datatype = DataType::Any,
                Rule::r#ref => is_ref = true,
                rule => unreachable!("Got rule {:?}", rule),
            };
        }
        Type { is_ref, datatype }
    }

    fn build_struct_type(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> String {
        let eval = pairs.peek().unwrap();
        eval.as_str().into()
    }

    fn build_int_type(&self, pairs: &mut Pairs<Rule>, context: &mut AstContext) -> DataType {
        let mut bytecount = 4;
        let mut is_unsigned = false;
        for pair in pairs {
            match pair.as_rule() {
                Rule::integer => bytecount = pair.as_str().parse().unwrap(),
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
