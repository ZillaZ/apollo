use super::{ast_context::AstContext, parser::Ast};

#[derive(Clone, Debug, PartialEq)]
pub struct Trait {
    pub name: String,
    pub fields: Vec<FieldDecl>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Operations {
    Add,
    Sub,
    Mul,
    Div,
    Neg,
    Eq,
    Neq,
    Lte,
    Gte,
    Lt,
    Gt,
    And,
    Or,
    Not,
    Modulo,
}

#[derive(Clone, Debug, PartialEq)]
pub struct UnaryOp {
    pub prefix: Operations,
    pub value: Box<Operation>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct BinaryOp {
    pub lhs: Box<Operation>,
    pub op: Operations,
    pub rhs: Box<Operation>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Type {
    pub is_ref: bool,
    pub ref_count: u8,
    pub datatype: DataType,
}

impl Default for Type {
    fn default() -> Self {
        Self {
            is_ref: false,
            ref_count: 0,
            datatype: DataType::Int(0),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum DataType {
    Float(u8),
    Int(u8),
    UInt(u8),
    Array(Box<ArrayType>),
    Struct(Box<StructDecl>),
    StructType(String),
    Trait(String),
    String,
    Char,
    Bool,
    Any,
}

impl ToString for DataType {
    fn to_string(&self) -> String {
        match self {
            DataType::Float(b) => format!("float{}", b),
            DataType::Any => "any".into(),
            DataType::Bool => "bool".into(),
            DataType::Char => "char".into(),
            DataType::Int(b) => format!("i{}", b),
            DataType::UInt(b) => format!("u{}", b),
            DataType::String => format!("string"),
            DataType::Array(_) => format!("array"),
            _ => panic!("{:?}", self),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Arg {
    pub name: Name,
    pub datatype: Type,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Operation {
    Atom(Atom),
    BinaryOp(BinaryOp),
    UnaryOp(UnaryOp),
}

#[derive(Clone, Debug, PartialEq)]
pub enum RefOp {
    Reference,
    Dereference,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Name {
    pub name: String,
    pub op: Option<RefOp>,
    pub op_count: u8,
}

impl Default for Name {
    fn default() -> Self {
        Self {
            name: String::new(),
            op: None,
            op_count: 0,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Parameter {
    Name(Name),
    Value(Value),
}

#[derive(Clone, Debug, PartialEq)]
pub enum AssignVar {
    Name(Name),
    Access(ArrayAccess),
    FieldAccess(FieldAccess),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Assignment {
    pub var: AssignVar,
    pub value: Value,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Call {
    pub neg: bool,
    pub name: Name,
    pub args: Vec<Parameter>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ArrayAccess {
    pub value: Value,
    pub index: Value,
}

#[derive(Clone, Debug, PartialEq)]
pub struct FieldDecl {
    pub name: String,
    pub datatype: Type,
}

#[derive(Clone, Debug, PartialEq)]
pub struct StructDecl {
    pub name: String,
    pub fields: Vec<FieldDecl>,
    pub traits: Vec<String>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum FieldAccessName {
    Name(Name),
    Call(Call),
    ArrayAccess(ArrayAccess),
}

#[derive(Clone, Debug, PartialEq)]
pub struct FieldAccess {
    pub op: Option<RefOp>,
    pub op_count: u8,
    pub name: FieldAccessName,
    pub next: Option<Box<FieldAccess>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Field {
    pub name: String,
    pub value: Parameter,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Constructor {
    pub name: String,
    pub fields: Vec<Field>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Casting((Box<Value>, String)),
    Operation(Box<Operation>),
    Call(Call),
    String(String),
    Int(i32),
    UInt(u32),
    Float(f32),
    Block(Box<Block>),
    Name(Name),
    Atom(Box<Atom>),
    Bool(bool),
    If(If),
    Char(char),
    Array(Array),
    ArrayAccess(Box<ArrayAccess>),
    Constructor(Box<Constructor>),
    FieldAccess(Box<FieldAccess>),
    Range(RangeValue),
}

#[derive(Clone, Debug, PartialEq)]
pub struct ArrayType {
    pub size: Value,
    pub data_type: Type,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Array {
    pub datatype: Type,
    pub elements: Vec<Value>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Return {
    pub value: Option<Value>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Block {
    pub expr: Vec<Box<Expr>>,
    pub box_return: Option<Return>,
}

impl Block {
    pub fn to_ast(&self) -> Ast {
        Ast {
            namespace: "nil".into(),
            expressions: self.expr.iter().map(|x| *x.clone()).collect::<Vec<_>>(),
            imports: std::collections::HashMap::new(),
            context: AstContext::new(),
        }
    }
    pub fn default() -> Block {
        Block {
            expr: Vec::new(),
            box_return: None,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum FunctionKind {
    Exported,
    External,
    Native,
}

impl FunctionKind {
    pub fn from_str(expr: &str) -> Self {
        match expr {
            "extern" => FunctionKind::External,
            "export" => FunctionKind::Exported,
            _ => unreachable!(),
        }
    }

    pub fn to_gcc_type(&self) -> gccjit::FunctionType {
        use self::FunctionKind::*;
        use gccjit::FunctionType;
        match self {
            Exported => FunctionType::Exported,
            External => FunctionType::Extern,
            Native => FunctionType::Internal,
            _ => unreachable!(),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Function {
    pub kind: FunctionKind,
    pub name: Name,
    pub args: Vec<Arg>,
    pub return_type: Option<Type>,
    pub block: Box<Block>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Declaration {
    pub name: Name,
    pub datatype: Option<Type>,
    pub value: Option<Value>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Atom {
    pub is_neg: bool,
    pub value: Value,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Impl {
    pub trait_name: String,
    pub struct_name: String,
    pub block: Block,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Otherwise {
    Block(Block),
    If(If),
}

#[derive(Clone, Debug, PartialEq)]
pub struct If {
    pub not: bool,
    pub condition: Box<Value>,
    pub block: Box<Block>,
    pub otherwise: Option<Box<Otherwise>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Extension {
    pub name: String,
    pub body: String,
}

#[derive(Clone, Debug, PartialEq)]
pub enum OverloadedOp {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Debug, PartialEq)]
pub enum OverloadedLHS {
    Name(Name),
    FieldAccess(FieldAccess),
}

#[derive(Clone, Debug, PartialEq)]
pub struct LibLink {
    pub lib_name: String,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Overloaded {
    pub lhs: OverloadedLHS,
    pub op: OverloadedOp,
    pub rhs: Value,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ImportKind {
    Dynamic,
    Static,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Import {
    pub kind: ImportKind,
    pub name: String,
    pub imported: Vec<String>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct WhileLoop {
    pub condition: Value,
    pub block: Box<Block>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ForLoop {
    pub pivot: String,
    pub range: Value,
    pub block: Block,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Range {
    pub start: Value,
    pub range_type: RangeType,
    pub end: Value,
}

#[derive(Clone, Debug, PartialEq)]
pub enum RangeValue {
    Iterable(Box<Value>),
    Range(Box<Range>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum RangeType {
    Inclusive,
    Exclusive,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Return(Return),
    Call(Call),
    Function(Function),
    Block(Block),
    Declaration(Declaration),
    If(If),
    Assignment(Assignment),
    Overloaded(Overloaded),
    Import(Import),
    StructDecl(StructDecl),
    FieldAccess(FieldAccess),
    Trait(Trait),
    Extension(Extension),
    Link(LibLink),
    While(WhileLoop),
    For(ForLoop),
    Impl(Impl),
}

impl Expr {
    pub fn import(&self) -> Import {
        match self {
            Expr::Import(import) => import.clone(),
            _ => panic!(),
        }
    }
}
