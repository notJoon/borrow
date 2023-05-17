#[derive(Debug, PartialEq)]
pub enum Statement {
    FunctionDef {
        name: String,
        args: Option<Vec<String>>,
        body: Vec<Statement>,
    },
    VariableDecl {
        name: String,
        value: Option<Expression>,
    },
    FunctionCall {
        name: String,
        args: Vec<Expression>,
    },
    Scope(Vec<Statement>),
}

/// A binary operator.
///
/// This is used to represent the binary operators in the AST.
#[derive(Debug, PartialEq)]
pub enum BinaryOp {
    Plus,
    Minus,
    Asterisk,
    Slash,
}

/// An expression.
///
/// This is used to represent the expressions in the AST.
#[derive(Debug, PartialEq)]
pub enum Expression {
    Ident(String),
    Number(i32),
    BinaryOp {
        lhs: Box<Expression>,
        op: BinaryOp,
        rhs: Box<Expression>,
    },
}
