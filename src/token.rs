#[derive(Debug, PartialEq, Clone)]
pub enum TokenType {
    Let,
    Fn,
    Ident(String),
    Equals,
    Number(i32),
    OpenBrace,
    CloseBrace,
    OpenParen,
    CloseParen,
    Comma,
}
