#[derive(Debug, PartialEq, Eq)]
pub enum ASTNode {
    VariableDecl {
        name: String,
        value: Box<ASTNode>,
    },
    FunctionDecl {
        name: String,
        params: Vec<String>,
        body: Box<ASTNode>,
    },
    FunctionCall {
        name: String,
        args: Vec<ASTNode>,
    },
    Number(i32),
    Ident(String),
    Scope(Vec<ASTNode>),
}
