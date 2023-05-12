#[derive(Debug, PartialEq)]
pub enum TokenType {
    Let,
    Ident(String),
    Equals,
    Number(i32),
    OpenBrace,
    CloseBrace,
}

