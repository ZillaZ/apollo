#[derive(Debug)]
pub enum Operations {
    Add,
    Sub,
    Mul,
    Div,
    Neg,
}

#[derive(Debug)]
pub struct UnaryOp {
    pub prefix: Operations,
    pub value: Box<MathOp>,
}

#[derive(Debug)]
pub struct BinaryOp {
    pub lhs: Box<MathOp>,
    pub op: Operations,
    pub rhs: Box<MathOp>,
}

#[derive(Debug)]
pub enum DataType {
    Float(u8),
    Int(u8),
    UFloat(u8),
    UInt(u8),
    String,
}

#[derive(Debug)]
pub struct Arg {
    pub name: String,
    pub datatype: DataType,
}

#[derive(Debug)]
pub enum MathOp {
    Atom(Atom),
    BinaryOp(BinaryOp),
    UnaryOp(UnaryOp),
}

#[derive(Debug)]
pub enum Parameter {
    Name(String),
    Value(Value),
}

#[derive(Debug)]
pub struct Call {
    pub name: String,
    pub args: Vec<Parameter>,
}

#[derive(Debug)]
pub enum Value {
    Math(Box<MathOp>),
    Call(Call),
    String(String),
    Int(i32),
    Float(f32),
    Block(Box<Block>),
    Name(String),
    Atom(Box<Atom>)
}

#[derive(Debug)]
pub struct Return {
    pub value: Value,
}

#[derive(Debug)]
pub struct Block {
    pub expr: Vec<Box<Expr>>,
    pub box_return: Option<Return>,
}

#[derive(Debug)]
pub struct Function {
    pub name: String,
    pub args: Vec<Arg>,
    pub return_type: Option<DataType>,
    pub block: Box<Block>,
}

#[derive(Debug)]
pub struct Declaration {
    pub name: String,
    pub datatype: DataType,
    pub value: Value,
}

#[derive(Debug)]
pub struct Atom {
    pub is_neg: bool,
    pub value: Value
}

#[derive(Debug)]
pub enum Expr {
    Return(Return),
    Call(Call),
    Function(Function),
    Block(Block),
    Declaration(Declaration),
}
