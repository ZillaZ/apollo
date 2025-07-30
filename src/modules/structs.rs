use gccjit::FunctionType;
use pest::iterators::{Pair, Pairs};

use crate::Rule;

use super::{ast_context::AstContext, parser::Ast};
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
};

#[derive(Clone, Debug, PartialEq)]
pub struct TraitMethod {
    pub name: String,
    pub params: Vec<Arg>,
    pub datatype: Option<Type>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Trait {
    pub name: String,
    pub generics: Vec<String>,
    pub methods: Vec<TraitMethod>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Operations {
    Add,
    Sub,
    Mul,
    Div,
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
    BitshiftLeft,
    BitshiftRight,
    BitAnd,
    BitOr,
    BitXor,
}

impl From<Pair<'_, Rule>> for Operations {
    fn from(value: Pair<Rule>) -> Self {
        use Operations::*;
        match value.as_rule() {
            Rule::add => Add,
            Rule::neg | Rule::sub => Sub,
            Rule::mul => Mul,
            Rule::div => Div,
            Rule::cmp_eq => Eq,
            Rule::neq => Neq,
            Rule::lte => Lte,
            Rule::gte => Gte,
            Rule::lt => Lt,
            Rule::gt => Gt,
            Rule::and => And,
            Rule::or => Or,
            Rule::not => Not,
            Rule::modulo => Modulo,
            Rule::bt_left => BitshiftLeft,
            Rule::bt_right => BitshiftRight,
            Rule::bt_or => BitOr,
            Rule::bt_and => BitAnd,
            Rule::bt_xor => BitXor,
            rule => unreachable!("Found rule {:?}", rule),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct UnaryOp {
    pub prefix: Operations,
    pub value: Rc<RefCell<Value>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct BinaryOp {
    pub lhs: Rc<RefCell<Value>>,
    pub op: Operations,
    pub rhs: Rc<RefCell<Value>>,
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

impl From<DataType> for Type {
    fn from(datatype: DataType) -> Self {
        Self {
            is_ref: false,
            ref_count: 0,
            datatype,
        }
    }
}

impl ToString for Type {
    fn to_string(&self) -> String {
        let prepend = (0..self.ref_count).map(|_| "&").collect::<String>();
        format!("{prepend}{}", self.datatype.to_string())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ExpandSection {
    Head,
    Tail,
}

#[derive(Clone, Debug, PartialEq)]
pub enum OsVariant {
    Windows,
    Linux,
}

impl OsVariant {
    pub fn is(&self, variant_str: &str) -> bool {
        variant_str
            == match self {
                OsVariant::Windows => "windows",
                OsVariant::Linux => "linux",
            }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Condition {
    Os(OsVariant),
}

#[derive(Clone, Debug, PartialEq)]
pub enum MacroKind {
    Expand(ExpandSection),
    Align(usize),
    Conditional(Condition),
    Packed,
}

impl From<&mut Pairs<'_, Rule>> for MacroKind {
    fn from(pairs: &mut Pairs<Rule>) -> Self {
        let pair = pairs.next().unwrap();
        let next = pairs.next().unwrap().into_inner().next().unwrap();
        match pair.as_rule() {
            Rule::name_str => match pair.as_str() {
                "expandable" => MacroKind::Expand(match next.as_str() {
                    "head" => ExpandSection::Head,
                    "tail" => ExpandSection::Tail,
                    _ => unreachable!(),
                }),
                "condition" => MacroKind::Conditional(match next.as_str() {
                    "os" => Condition::Os(match next.into_inner().next().unwrap().as_str() {
                        "windows" => OsVariant::Windows,
                        "linux" => OsVariant::Linux,
                        _ => unreachable!(),
                    }),
                    _ => unreachable!(),
                }),
                "alignment" => MacroKind::Align(next.as_str().parse::<usize>().unwrap()),
                "packed" => MacroKind::Packed,
                rule => unreachable!("Found {rule}"),
            },
            _ => unreachable!(),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Macro {
    pub macros: Vec<MacroKind>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct GenericType {
    pub base: String,
    pub generic: Type
}

impl ToString for GenericType {
    fn to_string(&self) -> String {
        format!("{}<{}>", self.base, self.generic.to_string())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct FunctionDatatype {
    pub datatype: Option<Type>,
    pub params: Vec<Type>
}

impl ToString for FunctionDatatype {
    fn to_string(&self) -> String {
        let params_str = self.params.iter().fold(String::new(), |acc, e| { format!("{acc},{}", e.to_string())  });
        let datatype_str = if let Some(ref dt) = self.datatype {
            format!("->{}", dt.to_string())
        }else{
            "".into()
        };
        format!("Fn({params_str}){datatype_str}")
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum DataType {
    Float(u8),
    Int(u8),
    UInt(u8),
    Array(Rc<RefCell<ArrayType>>),
    Struct(Rc<RefCell<StructDecl>>),
    StructType(String),
    Trait(String),
    String,
    Char,
    Bool,
    Any,
    Implements(Vec<String>),
    Generic(Rc<RefCell<GenericType>>),
    Function(Rc<RefCell<FunctionDatatype>>)
}

impl ToString for DataType {
    fn to_string(&self) -> String {
        match self {
            DataType::Float(b) => format!("float{}", b),
            DataType::Any => "any".into(),
            DataType::Bool => "bool".into(),
            DataType::Char => "char".into(),
            DataType::Int(b) => format!("i{}", b),
            DataType::UInt(b) => format!("ui{}", b),
            DataType::String => format!("string"),
            DataType::Array(_) => format!("array"),
            DataType::StructType(st) => st.clone(),
            DataType::Implements(ref traits) => traits.iter().fold(String::from("impls "), |acc, e| { format!("{acc} {e}")}),
            DataType::Generic(ref rc) => {
                let generic = rc.borrow();
                generic.to_string()
            }
            _ => panic!("{:?}", self),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
struct VariadicValue(i32);

#[derive(Clone, Debug, PartialEq)]
pub struct Arg {
    pub name: Name,
    pub datatype: Type,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Operation {
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
    pub args: Vec<Value>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ArrayAccess {
    pub value: Value,
    pub index: Value,
}

#[derive(Clone, Debug, PartialEq)]
pub struct TraitType {
    pub name: String,
    pub implements: Vec<String>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct FieldDecl {
    pub name: String,
    pub datatype: Type,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Attribute {
    pub name: String,
    pub value: ValueEnum,
}

#[derive(Clone, Debug, PartialEq)]
pub struct StructDecl {
    pub name: String,
    pub fields: Vec<FieldDecl>,
    pub attributes: Vec<Attribute>,
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
    pub next: Rc<RefCell<Option<FieldAccess>>>,
}

impl Default for FieldAccess {
    fn default() -> Self {
        Self {
            op: None,
            op_count: 0,
            name: FieldAccessName::Name(Name::default()),
            next: Rc::new(RefCell::new(None)),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Field {
    pub name: String,
    pub value: Value,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Constructor {
    pub name: String,
    pub fields: Vec<Field>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct EnumValue {
    pub datatype: String,
    pub variant: String,
    pub inner: Option<Value>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ValueEnum {
    Casting((Rc<RefCell<Value>>, Type)),
    BinaryOp(Rc<RefCell<BinaryOp>>),
    UnaryOp(Rc<RefCell<UnaryOp>>),
    Call(Call),
    String(String),
    Int(i32),
    UInt(u32),
    Float(f32),
    Closure(Rc<RefCell<Closure>>),
    Name(Name),
    Bool(bool),
    If(If),
    Char(char),
    Array(Array),
    ArrayAccess(Rc<RefCell<ArrayAccess>>),
    Constructor(Rc<RefCell<Constructor>>),
    FieldAccess(Rc<RefCell<FieldAccess>>),
    Range(RangeValue),
    Enum(Rc<RefCell<EnumValue>>),
    Match(Rc<RefCell<Match>>),
    None,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Value {
    pub heap_allocated: bool,
    pub value: ValueEnum,
}

impl Default for Value {
    fn default() -> Self {
        Self {
            heap_allocated: false,
            value: ValueEnum::Int(0),
        }
    }
}

impl Value {
    pub fn non_heap(value: ValueEnum) -> Self {
        Self {
            heap_allocated: false,
            value,
        }
    }
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

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Block {
    pub expr: Vec<Rc<RefCell<Expr>>>,
    pub box_return: Option<Return>,
}

impl Block {
    pub fn to_ast(
        &mut self,
        namespace: String,
        context: AstContext,
        core_context: AstContext,
    ) -> Ast {
        Ast {
            namespace,
            context,
            expressions: self
                .expr
                .iter_mut()
                .map(|x| Rc::make_mut(x).get_mut().clone())
                .collect::<Vec<_>>(),
            imports: HashMap::new(),
            core_context,
        }
    }
    pub fn default() -> Block {
        Block {
            expr: Vec::new(),
            box_return: None,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq)]
pub enum FunctionKind {
    Exported,
    External,
    #[default]
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
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Closure {
    pub args: Vec<String>,
    pub block: Rc<RefCell<Block>>,
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Function {
    pub kind: FunctionKind,
    pub name: Name,
    pub args: Vec<Arg>,
    pub return_type: Option<Type>,
    pub block: Rc<RefCell<Block>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Declaration {
    pub name: Name,
    pub datatype: Option<Type>,
    pub value: Option<Value>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ImplType {
    pub name: String,
    pub implements: Vec<String>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ImplMethod {
    pub name: String,
    pub params: Vec<Arg>,
    pub datatype: Option<Type>,
    pub body: Block,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Impl {
    pub trait_name: String,
    pub target_name: Option<String>,
    pub generics: Vec<(String, String)>,
    pub methods: Vec<ImplMethod>,
}

impl Default for Impl {
    fn default() -> Self {
        Self {
            trait_name: String::new(),
            target_name: None,
            generics: Vec::new(),
            methods: Vec::new(),
        }
    }
}

impl From<&mut ImplMethod> for Function {
    fn from(value: &mut ImplMethod) -> Self {
        let name = value.name.clone();
        Self {
            name: Name {
                name,
                op: None,
                op_count: 0,
            },
            kind: FunctionKind::Native,
            args: value.params.clone(),
            return_type: value.datatype.clone(),
            block: Rc::new(RefCell::new(value.body.clone())),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Otherwise {
    Block(Block),
    If(If),
}

#[derive(Clone, Debug, PartialEq)]
pub struct EnumMatch {
    pub name: String,
    pub variant: String,
    pub var: String,
}

#[derive(Clone, Debug, PartialEq)]
pub struct If {
    pub not: bool,
    pub condition: Option<Rc<RefCell<Value>>>,
    pub enum_match: Option<EnumMatch>,
    pub block: Rc<RefCell<Block>>,
    pub otherwise: Option<Rc<RefCell<Otherwise>>>,
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

#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Namespace {
    pub name: String,
    pub next: Vec<Box<Namespace>>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Import {
    pub kind: ImportKind,
    pub namespace: Namespace,
}

#[derive(Clone, Debug, PartialEq)]
pub struct WhileLoop {
    pub condition: Value,
    pub block: Rc<RefCell<Block>>,
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
    Iterable(Rc<RefCell<Value>>),
    Range(Rc<RefCell<Range>>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum RangeType {
    Inclusive,
    Exclusive,
}

#[derive(Clone, Debug, PartialEq)]
pub struct EnumVariant {
    pub name: String,
    pub r#type: Option<Type>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Enum {
    pub name: String,
    pub variants: Vec<EnumVariant>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct AsmArg {
    pub constraint: String,
    pub value: ValueEnum,
    pub name: Option<String>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Assembly {
    pub volatile: bool,
    pub asm: String,
    pub input: Vec<AsmArg>,
    pub output: Vec<AsmArg>,
    pub clobbered: Vec<String>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum MatchCaseValue {
    Default,
    Value(ValueEnum)
}

#[derive(Clone, Debug, PartialEq)]
pub struct MatchCase {
    pub value: MatchCaseValue,
    pub expr: Vec<Expr>
}

#[derive(Clone, Debug, PartialEq)]
pub struct Match {
    pub value: ValueEnum,
    pub cases: Vec<MatchCase>
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Return(Return),
    Call(Call),
    MacroCall(Call),
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
    Link(LibLink),
    While(WhileLoop),
    For(ForLoop),
    Impl(Impl),
    Enum(Enum),
    Assembly(Assembly),
    VariadicBlock(Block),
    Macro(Macro),
    Match(Match)
}

impl Expr {
    pub fn import(&self) -> Import {
        match self {
            Expr::Import(import) => import.clone(),
            _ => panic!(),
        }
    }
}
