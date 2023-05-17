#[derive(Debug, PartialEq)]
pub enum Statement {
    /// Represents a function definition.
    ///
    /// Contains the name of the function, optional arguments,
    /// and the body of the function as a vector of statements.
    FunctionDef {
        name: String,
        args: Option<Vec<String>>,
        body: Vec<Statement>,
    },
    /// Represents a variable declaration.
    ///
    /// Contains the name of the variable, an optional value,
    /// and a flag indicating whether the variable is borrowed.
    VariableDecl {
        name: String,
        value: Option<Expression>,
        is_borrowed: bool,
    },
    /// Represents a function call.
    ///
    /// Contains the name of the function and the arguments
    /// passed to the function as a vector of expressions.
    FunctionCall {
        name: String,
        args: Vec<Expression>,
    },
    /// Represents a scope or block of statements.
    ///
    /// Contains a vector of statements representing the
    /// statements enclosed within the scope.
    Scope(Vec<Statement>),
}

/// A binary operator.
///
/// Used to represent binary operators in the AST.
#[derive(Debug, PartialEq)]
pub enum BinaryOp {
    Plus,
    Minus,
    Asterisk,
    Slash,
}

/// An expression.
///
/// Used to represent expressions in the AST.
#[derive(Debug, PartialEq)]
pub enum Expression {
    /// Represents an identifier.
    ///
    /// Contains the name of the identifier as a string.
    Ident(String),
    /// Represents a numeric literal.
    ///
    /// Contains the value of the number as an i32.
    Number(i32),
    /// Represents a binary operation.
    ///
    /// Contains the left-hand side expression, the binary operator,
    /// and the right-hand side expression, all wrapped in boxes.
    BinaryOp {
        lhs: Box<Expression>,
        op: BinaryOp,
        rhs: Box<Expression>,
    },
    /// Represents a reference to a variable.
    ///
    /// Contains the name of the referenced variable as a string.
    Reference(String),
}
