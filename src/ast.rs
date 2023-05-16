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
        arg: Option<Expression>,
    },
    Scope(Vec<Statement>),
}

#[derive(Debug, PartialEq)]
pub enum Expression {
    Ident(String),
    Number(i32),
}
