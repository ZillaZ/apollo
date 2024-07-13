#[derive(Clone, Debug, PartialEq)]
pub struct Trait {
    pub name: String,
    pub fields: Vec<FieldDecl>
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
    Modulo
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
    pub datatype: DataType
}

impl Default for Type {
    fn default() -> Self {
        Self {
            is_ref: false,
            datatype: DataType::Int(0)
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
    Dereference
}

#[derive(Clone, Debug, PartialEq)]
pub struct Name {
    pub name: String,
    pub op: Option<RefOp>
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
    FieldAccess(FieldAccess)
}

#[derive(Clone, Debug, PartialEq)]
pub struct Assignment {
    pub var: AssignVar,
    pub value: Value
}

#[derive(Clone, Debug, PartialEq)]
pub struct Call {
    pub name: Name,
    pub args: Vec<Parameter>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ArrayAccess {
    pub value: Value,
    pub index: Value
}

#[derive(Clone, Debug, PartialEq)]
pub struct FieldDecl {
    pub name: String,
    pub datatype: Type
}

#[derive(Clone, Debug, PartialEq)]
pub struct StructDecl {
    pub name: String,
    pub fields: Vec<FieldDecl>,
    pub traits: Vec<String>
}

#[derive(Clone, Debug, PartialEq)]
pub enum FieldAccessName {
    Name(Name),
    Call(Call),
    ArrayAccess(ArrayAccess)
}

#[derive(Clone, Debug, PartialEq)]
pub struct FieldAccess {
    pub name: FieldAccessName,
    pub next: Option<Box<FieldAccess>>
}

#[derive(Clone, Debug, PartialEq)]
pub struct Field {
    pub name: String,
    pub value: Parameter
}

#[derive(Clone, Debug, PartialEq)]
pub struct Constructor {
    pub name: String,
    pub fields: Vec<Field>
}

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Operation(Box<Operation>),
    Call(Call),
    String(String),
    Int(i32),
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
    FieldAccess(Box<FieldAccess>)
}

#[derive(Clone, Debug, PartialEq)]
pub struct ArrayType {
    pub size: Value,
    pub data_type: Type
}

#[derive(Clone, Debug, PartialEq)]
pub struct Array {
    pub array_type: Box<ArrayType>,
    pub elements: Vec<Value>
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

#[derive(Clone, Debug, PartialEq)]
pub struct Function {
    pub is_extern: bool,
    pub name: Name,
    pub args: Vec<Arg>,
    pub return_type: Option<Type>,
    pub block: Box<Block>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Declaration {
    pub name: Name,
    pub datatype: Option<Type>,
    pub value: Value,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Atom {
    pub is_neg: bool,
    pub value: Value
}

#[derive(Clone, Debug, PartialEq)]
pub enum Otherwise {
    Block(Block),
    If(If)
}

#[derive(Clone, Debug, PartialEq)]
pub struct If {
    pub not: bool,
    pub condition: Box<Operation>,
    pub block: Box<Block>,
    pub otherwise: Option<Box<Otherwise>>
}

#[derive(Clone, Debug, PartialEq)]
pub enum OverloadedOp {
    Add,
    Sub,
    Mul,
    Div
}

#[derive(Clone, Debug, PartialEq)]
pub enum OverloadedLHS {
    Name(Name),
    FieldAccess(FieldAccess)
}

#[derive(Clone, Debug, PartialEq)]
pub struct Overloaded {
    pub lhs: OverloadedLHS,
    pub op: OverloadedOp,
    pub rhs: Value
}

#[derive(Clone, Debug, PartialEq)]
pub enum ImportKind {
    Dynamic,
    Static
}

#[derive(Clone, Debug, PartialEq)]
pub struct Import {
    pub kind: ImportKind,
    pub name: String
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
    Trait(Trait)
}

impl Expr {
    pub fn import(&self) -> Import {
        match self {
            Expr::Import(import) => import.clone(),
            _ => panic!()
        }
    }
}
